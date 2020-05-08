(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Nikhil Swamy, ...
*)

#light "off"
module FStar.TypeChecker.DeferredImplicits
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Ident
open FStar.TypeChecker.Common
open FStar.Syntax
module BU = FStar.Util
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst

let is_flex t =
    let head, _args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar _ -> true
    | _ -> false

let flex_uvar_head t =
    let head, _args = U.head_and_args t in
    match (SS.compress head).n with
    | Tm_uvar (u, _) -> u
    | _ -> failwith "Not a flex-uvar"

type goal_type =
  | FlexRigid of ctx_uvar * term
  | FlexFlex of ctx_uvar * ctx_uvar
  | Can_be_split_into of term * term * ctx_uvar
  | Imp of ctx_uvar

type goal_dep =
  {
    goal_dep_id:int;       //Assign each goal an id, for cycle detection
    goal_type:goal_type; //What sort of goal ...
    goal_imp:implicit;   //The entire implicit from which this was generated
    assignees:BU.set<ctx_uvar>; //The set of uvars assigned by the goal
    goal_dep_uvars:BU.set<ctx_uvar>; //The set of uvars this goal depends on
    dependences:ref<goal_deps>; //NB: mutable; the goals that must precede this one in the order
    visited:ref<int> //NB: mutable; a field to mark visited goals during the sort
  }
and goal_deps = list<goal_dep>

let print_uvar_set (s:BU.set<ctx_uvar>) =
    (BU.set_elements s
     |> List.map (fun u -> "?" ^ (string_of_int <| Unionfind.uvar_id u.ctx_uvar_head))
     |> String.concat "; ")

let print_goal_dep gd =
  BU.format4 "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n"
    (BU.string_of_int gd.goal_dep_id)
    (print_uvar_set gd.assignees)
    (List.map (fun gd -> string_of_int gd.goal_dep_id) (!gd.dependences)
     |> String.concat "; ")
    (Print.ctx_uvar_to_string gd.goal_imp.imp_uvar)

(** This function is called by the typechecker to sort all the goals
    before dispatching control to a user-provided tactic to solve
    those goals.

    - [env]: This is the current typechecking environment, currently
      mainly used for debugging

    - [imps]: All deferred constraints.

      E.g., if the typechecker
      generated and deferred a constraint, [?pre_f = t], this
      constraint appears in this list in the form of a goal
      [?witness : (eq2 #tf ?pre_f t)], where [tf] is the type of [pre_f].

      E.g., if the
      typechecker generated and deferred solving an implicit variable
      and [?frame : hprop] or
      [?u : squash (can_be_split_into outer inner frame)], these constraints
      appear in this list.

   [sort_goals] gathers all these constraints into a single list of
   implicits sorted in a topological order based on dependences among
   the unsolved implicit variables.

   Limitations:

     - Arguably, this code should not be in the compiler at all, and
       should instead be handled in user-land by a tactic. We could do
       that in the long run, after stabilizing the behavior of this
       code. For now, it's easier to experiment with support within
       the compiler, while also benefiting immediately with native
       compilation.

     - This code is very specific to
       [Steel.Memory.Tactics.can_be_split_into] Aymeric suggested (and
       it's well worth doing) to generalize it so that we add an
       attribute to a predicate signaling which variables it depends
       on and which variables it assignes. E.g., for
       can_be_split_into, we could have

       {[
         [@(dependences (Assigns [2]) (DependsOn [0; 1]))]
         let can_be_split_into (outer inner frame:hprop) = ...
       ]}
*)
let sort_goals (env:FStar.TypeChecker.Env.env) (imps:implicits) : implicits =
  (* For each goal g, maintain:
       1. Assigned uvars, at most 2 of them
           - if g is a flex_rigid eq goal, then it assigns one uvar
           - if g is a flex_flex eq goal, then it assigns two uvars
           - if g is a can_be_split_into outer inner frame, then it assigns frame
           - otherwise g assigns no uvars

       2. A list of goals that are dependences for each goal LHS
          - if g is a flex_rigid goal (?lhs = rhs) then it depends on
               all goals g' that may assign a variable in freeuvars rhs

          - if g is a flex_flex goal (?lhs = ?rhs) then it depends on
               all goals g' that may assign either lhs or rhs

          - if g is a ?u:split_frame outer inner, then it depends on
               all goals g' that may assign a variable in freeuvars outer U freeuvars inner

          - otherwise g's dependence is Top (meaning these goals depend on all other goals)

       3. Given the dependence relations among all the goals, topologically sort them

     We need to take special care to avoid cycles, and in particular
     to compute dependences among the flex_flex goals. See below.
  *)
  //A counter for the ids
  let goal_dep_id = BU.mk_ref 0 in
  //Three tags for the topological sort
  let mark_unset, mark_inprogress, mark_finished = 0, 1, 2 in
  //Functional (ie., immutable) sets of uvars
  let empty_uv_set = Free.new_uv_set () in
  (** Converting an implicit into a goal_dep:
        -- Determines the case of an equality goal (Flex_flex, Flex_right etc.)
        -- Inteprets can_be_split_into
   *)
  let imp_as_goal_dep (imp:implicit) =
      BU.incr goal_dep_id;
      match (imp.imp_uvar.ctx_uvar_typ).n with
      | Tm_app({n=Tm_uinst({n=Tm_fvar fv}, _)}, [_; (lhs, _); (rhs, _)])
              when S.fv_eq_lid fv FStar.Parser.Const.eq2_lid ->
        let flex_lhs = is_flex lhs in
        let flex_rhs = is_flex rhs in
        let goal_type, assignees, dep_uvars =
          if flex_lhs && flex_rhs
          then let lhs, rhs = flex_uvar_head lhs, flex_uvar_head rhs in
               let assignees = BU.set_add rhs (BU.set_add lhs empty_uv_set) in
               //Note, for a flex-flex, the assignees and the dep_uvars are the same
               //If we're not careful below, this will induce cycles in the graph
               //immediately. See handling in fill_deps
               FlexFlex (lhs, rhs), assignees, assignees
          else if flex_lhs
          then let lhs = flex_uvar_head lhs in
               let assignees = BU.set_add lhs empty_uv_set in
               let dep_uvars = Free.uvars rhs in
               FlexRigid (lhs, rhs), assignees, dep_uvars
          else if flex_rhs
          then let rhs = flex_uvar_head rhs in
               let assignees = BU.set_add rhs empty_uv_set in
               let dep_uvars = Free.uvars lhs in
               FlexRigid (rhs, lhs), assignees, dep_uvars
          else failwith "Impossible: deferred goals must be flex on one at least one side"
        in
        { goal_dep_id = !goal_dep_id;
          goal_type = goal_type;
          goal_imp = imp;
          assignees = assignees;
          goal_dep_uvars = dep_uvars;
          dependences = BU.mk_ref [];
          visited = BU.mk_ref mark_unset }

      | _ ->
        let imp_goal () =
            if Env.debug env <| Options.Other "ResolveImplicitsHook"
            then BU.print1 "Goal is a generic implicit: %s\n" (Print.term_to_string imp.imp_uvar.ctx_uvar_typ);
            { goal_dep_id = !goal_dep_id;
              goal_type = Imp(imp.imp_uvar);
              goal_imp = imp;
              assignees = empty_uv_set;
              goal_dep_uvars = empty_uv_set;
              dependences = BU.mk_ref [];
              visited = BU.mk_ref mark_unset }
        in
        match U.un_squash imp.imp_uvar.ctx_uvar_typ with
        | None -> imp_goal()
        | Some t ->
            let head, args = U.head_and_args t in
            //Here, rather than matching specifically on this type
            //We could consult the [env] for attributes on fv to see if is
            //tagged with any dependence annotations and process it accordingly
            match (U.un_uinst head).n, args with
            | Tm_fvar fv, [(outer, _);(inner, _);(frame, _)]
                when fv_eq_lid fv (Ident.lid_of_str "Steel.Memory.Tactics.can_be_split_into")
                && is_flex frame ->
              let imp_uvar = flex_uvar_head frame in
              { goal_dep_id = !goal_dep_id;
                goal_type = Can_be_split_into(outer, inner, imp_uvar);
                goal_imp = imp;
                assignees = BU.set_add imp_uvar empty_uv_set;
                goal_dep_uvars = BU.set_union (Free.uvars outer) (Free.uvars inner);
                dependences = BU.mk_ref [];
                visited = BU.mk_ref mark_unset }
            | _ -> imp_goal()
  in
  let goal_deps = List.map imp_as_goal_dep imps in
  //We split out the Imp goals into [rest] and will not consider them
  //during the sort ... they'll all just go at the end
  let goal_deps, rest =
    List.partition
      (fun gd -> match gd.goal_type with
              | Imp _ -> false
              | _ -> true)
      goal_deps
  in

  (** [fill_deps] does the main conceptual work, building a graph
      among the goals by filling the [dependences] edges for each
      [goal_dep] node.

      It does this iteratively until fixed point.

      At each iteration, it considers each goal [gd] in turn and
      considers whether or not it should depend on any other goal
      [other_gd].

      - If gd.goal_dep_id == other_gd.goal_dep_id, then no edge is
        added, since this would be a self loop.

      - Otherwise, if [other_gd.assignees] overlaps with
        [gd.goal_dep_uvar] then a solution to [other_gd] could
        constrain the solution of [gd], so [other_gd] should precede
        [gd] in the order. i.e., we should add an edge from [gd] to
        [other_gd]. But, we need to be careful. Consider the
        following:

        {[
          gd       = (?u0 = ?u1);
          other_gd = (?u0 = ?u2)
         ]}

        In this case, [gd]'s assignee set overlaps with other_gd's
        goal_dep_uvars set, and vice versa. So, if we're not careful,
        we'll get a cycle between these two nodes.

        The way we handle this is to say that if [other_gd] is a
        FlexFlex node, then [gd] depend on [other_gd] only if

          1. [other_gd.dependences] is non-empty: meaning that
             [other_gd]

          2. And, if [other_gd.dependences] does not contain [gd]

        That is, [other_gd] has a non-trivial constraint on some other
        node that is already scheduled.

        Note, to implement the cycle detection in step 2 above, the
        [dependences] field of each node maintains the set of
        **reachable** nodes, not just the immediate dependences.

        There are many opportunities for improving the efficiency of
        this code. Currently, most operations are done using a full
        scan of the list of goal_deps, making the inner loop
        quadratic, and the whole thing is cubic or more in the nubmer
        of nodes. One obvious improvement would be to maintain the
        nodes in a hash map, so that lookup (using goal_dep_id) is
        constant time.
   *)
  let fill_deps gds : unit  =
    let in_deps (deps:list<goal_dep>) (gd:goal_dep) =
      BU.for_some (fun d -> d.goal_dep_id = gd.goal_dep_id) deps
    in
    let fill_deps_of_goal (gd:goal_dep) : bool =
      let dependent_uvars = gd.goal_dep_uvars in
      let current_deps = !gd.dependences in
      let changed = BU.mk_ref false in
      let deps =
        List.filter
           (fun other_gd ->
             let res =
               if gd.goal_dep_id = other_gd.goal_dep_id
               then false // no self-dependences
               else if in_deps current_deps other_gd
               then false //no duplicates; it's already in the dep list
                          //Don't add it, or else we will falsely signal
                          //that the graph changed an the fixed point will
                          //not converge
               else match other_gd.goal_type with
                    | FlexFlex _ ->
                      begin
                      match !other_gd.dependences with
                      | [] ->
                        //See case 1 of the comment above
                        false //this flex-flex is not yet schedulable
                      | deps ->
                        //it has non-trivial dependences and no cycles
                        //allowed. See case 2 of the comment above.
                        let eligible = not (in_deps deps gd) in
                        if eligible
                        then not (BU.set_is_empty (BU.set_intersect dependent_uvars other_gd.assignees))
                        else false
                      end
                    | _ ->
                      not (BU.set_is_empty (BU.set_intersect dependent_uvars other_gd.assignees))
             in
             if res then changed := true;
             res)
            gds
      in
      if Env.debug env <| Options.Other "ResolveImplicitsHook"
      then
        BU.print3 "Deps for goal %s, dep uvars = %s ... [%s]\n"
                (print_goal_dep gd)
                (print_uvar_set dependent_uvars)
                ((List.map (fun x -> string_of_int x.goal_dep_id) deps |> String.concat "; "));
      gd.dependences := deps @ !gd.dependences;
      !changed
    in
    //The outer fixed point loop
    let rec aux () =
      let changed =
        List.fold_right
          (fun gd changed ->
            let changed' = fill_deps_of_goal gd in
            changed || changed')
          gds false
      in
      if changed then aux() else ()
    in
    aux()
  in
  (** Given a graph of goal_dep nodes, sort them topologically
      using a depth-first traversal *)
  let topological_sort gds =
    let out = BU.mk_ref [] in
    let has_cycle = BU.mk_ref false in
    let rec visit cycle gd =
      if !gd.visited = mark_finished then ()
      else if !gd.visited = mark_inprogress
      then let _ =
            if Env.debug env <| Options.Other "ResolveImplicitsHook"
            then
               BU.print1 "Cycle:\n%s\n"
                 (List.map print_goal_dep (gd::cycle) |> String.concat ", ")
           in
           has_cycle := true
      else begin
        gd.visited := mark_inprogress;
        List.iter (visit (gd::cycle)) !gd.dependences;
        gd.visited := mark_finished;
        out := gd :: !out
      end
    in
    List.iter (visit []) gds;
    if !has_cycle then None else Some (!out)
  in
  fill_deps goal_deps;
  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then (BU.print_string "<<<<<<<<<<<<Goals before sorting>>>>>>>>>>>>>>>\n";
        List.iter (fun gd -> BU.print_string (print_goal_dep gd)) goal_deps);
  let goal_deps =
    match topological_sort goal_deps with
    | None -> goal_deps
    | Some sorted -> List.rev sorted //we actually want reverse topo sort
  in
  if Env.debug env <| Options.Other "ResolveImplicitsHook"
  then (BU.print_string "<<<<<<<<<<<<Goals after sorting>>>>>>>>>>>>>>>\n";
        List.iter (fun gd -> BU.print_string (print_goal_dep gd)) goal_deps);
  List.map (fun gd -> gd.goal_imp) (goal_deps @ rest)

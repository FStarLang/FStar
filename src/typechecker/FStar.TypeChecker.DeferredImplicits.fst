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

   Authors: Nikhil Swamy
*)

module FStar.TypeChecker.DeferredImplicits
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Compiler.Util
open FStar.Errors
open FStar.TypeChecker
open FStar.Syntax
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Ident
open FStar.TypeChecker.Common
open FStar.Syntax
module BU = FStar.Compiler.Util
module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util
module SS = FStar.Syntax.Subst

let is_flex t =
  let head, _args = U.head_and_args_full t in
  match (SS.compress head).n with
  | Tm_uvar _ -> true
  | _ -> false

let flex_uvar_head t =
    let head, _args = U.head_and_args_full t in
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
    assignees:BU.set ctx_uvar; //The set of uvars assigned by the goal
    goal_dep_uvars:BU.set ctx_uvar; //The set of uvars this goal depends on
    dependences:ref goal_deps; //NB: mutable; the goals that must precede this one in the order
    visited:ref int //NB: mutable; a field to mark visited goals during the sort
  }
and goal_deps = list goal_dep

let print_uvar_set (s:BU.set ctx_uvar) =
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

(*
  If [u] is tagged with attribute [a]

  We look in the context for definitions tagged with [@@resolve_implicits; a]
  These are the initial [candidates]
  
  We filter the [candidates] to find a unique candidate [c], such that
  [c] is not overridden and it overrides all other all other
  [candidates]. 

  A candidate [c] overriders [c'] if [c] contains the attribute

   override_resolve_implicits_handler a [l]

  and [l] contains the name of [c]

  If no candidates are found we return None
  If no unique [c] exists we warn and return None
*)
let find_user_tac_for_uvar env (u:ctx_uvar) : option sigelt =
    (* This tries to unembed a Cons (Tm_constant (Const_string s1))
                               ...
                               Cons (Tm_constant (Const_string sn))
                               Nil
       to [s1;..;sn]                               
       
       It's a bit ugly because the term it is applied to [e]
       is just an attribute, and so it is not actually a type-correct term.
       
       So, the type arguments of the Cons may be missing *)
    let rec attr_list_elements (e:term) : option (list string) =
      let head, args = U.head_and_args (U.unmeta e) in
      match (U.un_uinst head).n, args with
      | Tm_fvar fv, _ when fv_eq_lid fv FStar.Parser.Const.nil_lid ->
        Some []
      | Tm_fvar fv, [_; (hd, _); (tl, _)] 
      | Tm_fvar fv, [(hd, _); (tl, _)]     
        when fv_eq_lid fv FStar.Parser.Const.cons_lid ->
        (match hd.n with
         | Tm_constant (FStar.Const.Const_string (s, _)) -> 
           (match attr_list_elements tl with
            | None -> None
            | Some tl -> Some (s::tl))
         | _ -> None)
      | _ ->
        None
    in
    let candidate_names candidates = 
          List.collect U.lids_of_sigelt candidates
          |> List.map string_of_lid
          |> String.concat ", "
    in
    match u.ctx_uvar_meta with
    | Some (Ctx_uvar_meta_attr a) ->
      (* hooks: all definitions with the resolve_implicits attr *)
      let hooks = Env.lookup_attr env FStar.Parser.Const.resolve_implicits_attr_string in
      (* candidates: hooks that also have the attribute [a] *)
      let candidates = 
        hooks |> List.filter
                  (fun hook -> hook.sigattrs |> BU.for_some (U.attr_eq a))
      in
      (* The environment sometimes returns duplicates in the candidate list; filter out dups *)
      let candidates =
        BU.remove_dups
          (fun s0 s1 -> 
            let l0 = U.lids_of_sigelt s0 in
            let l1 = U.lids_of_sigelt s1 in
            if List.length l0 = List.length l1
            then List.forall2 (fun l0 l1 -> Ident.lid_equals l0 l1) l0 l1
            else false)
          candidates
      in
      (* Checking if a candidate is overridden, by scanning the list of all 
         candidates and seeing if any of them override it *)
      let is_overridden (candidate:sigelt)
        : bool
        = (* A candidate may have more than one lid, in case it is a let rec
             It is overridden if any of its names are overridden *)
          let candidate_lids = U.lids_of_sigelt candidate in
          candidates |>
          BU.for_some 
            (fun (other:sigelt) ->
               other.sigattrs |>
               BU.for_some 
               (fun attr -> 
                 let head, args = U.head_and_args attr in
                 match (U.un_uinst head).n, args with
                 | Tm_fvar fv, [_; (a', _); (overrides, _)] //type argument may be missing, since it is just an attr
                 | Tm_fvar fv, [(a', _); (overrides, _)]                 
                   when fv_eq_lid fv FStar.Parser.Const.override_resolve_implicits_handler_lid
                     && U.attr_eq a a' ->
                   //other has an attribute [@@override_resolve_implicits_handler a overrides]
                   begin
                   match attr_list_elements overrides with
                   | None -> false
                   | Some names ->
                     //if the overrides mention one of the candidate's names
                     //the candidate is overriden
                     names |>
                     BU.for_some (fun n -> 
                       candidate_lids |> BU.for_some (fun l -> string_of_lid l = n))
                   end
                 | _ -> false))
      in
      let candidates = candidates |> List.filter (fun c -> not (is_overridden c)) in
      begin
      match candidates with
      | [] -> None //no candidates
      | [ c ] -> Some c //if there is a unique candidate return it
      | _ -> //it is ambiguous; complain
        let candidates = candidate_names candidates in
        let attr = Print.term_to_string a in
        FStar.Errors.log_issue u.ctx_uvar_range
                               (FStar.Errors.Warning_AmbiguousResolveImplicitsHook,
                                BU.format2
                                  "Multiple resolve_implicits hooks are eligible for attribute %s; \n\
                                   please resolve the ambiguity by using the `override_resolve_implicits_handler` attribute \
                                   to choose among these candidates {%s}"
                                   attr candidates);
        None
      end
      
    | _ -> None

let should_defer_uvar_to_user_tac env (u:ctx_uvar) =
  if not env.enable_defer_to_tac then false
  else Option.isSome (find_user_tac_for_uvar env u)


let solve_goals_with_tac env g (deferred_goals:implicits) (tac:sigelt) =
  Profiling.profile (fun () ->
    let resolve_tac =
      match tac.sigel with
      | Sig_let (_, [lid]) ->
        let qn = Env.lookup_qname env lid in
        let fv = S.lid_as_fv lid (Delta_constant_at_level 0) None in
        let dd =
          match Env.delta_depth_of_qninfo fv qn with
          | Some dd -> dd
          | None -> failwith "Expected a dd"
        in
        let term = S.fv_to_tm (S.lid_as_fv lid dd None) in
        term
      | _ -> failwith "Resolve_tac not found"
    in
    let env = { env with enable_defer_to_tac = false } in
    env.try_solve_implicits_hook env resolve_tac deferred_goals)
  (Some (Ident.string_of_lid (Env.current_module env)))
  "FStar.TypeChecker.DeferredImplicits.solve_goals_with_tac"

(** This functions is called in Rel.force_trivial_guard to solve all
    goals in a guard that were deferred to a tactic *)
let solve_deferred_to_tactic_goals env g =
    if not env.enable_defer_to_tac then g else
    let deferred = g.deferred_to_tac in
    (** A unification problem between two terms is presented to
        a tactic as an equality goal between the terms. *)
    let prob_as_implicit (_, reason, prob)
      : implicit * sigelt =
      match prob with
      | TProb tp when tp.relation=EQ ->
        let env, _ = Env.clear_expected_typ env in
        let env = {env with gamma=tp.logical_guard_uvar.ctx_uvar_gamma} in
        let env_lax = {env with lax=true; use_bv_sorts=true; enable_defer_to_tac=false} in
        let _, t_eq, _ =
          //Prefer to use the type of the flex term to compute the
          //type instantiation of the equality, since it is more efficient
          let t =
            if is_flex tp.lhs then tp.lhs
            else tp.rhs
          in
          env.typeof_tot_or_gtot_term env_lax t true  //AR: TODO: can we call type_of_well_typed?
        in
        let goal_ty = U.mk_eq2 (env.universe_of env_lax t_eq) t_eq tp.lhs tp.rhs in
        let goal, ctx_uvar, _ =
            Env.new_implicit_var_aux reason tp.lhs.pos env goal_ty Strict None
        in
        let imp =
            { imp_reason = "";
              imp_uvar = fst (List.hd ctx_uvar);
              imp_tm = goal;
              imp_range = tp.lhs.pos
            }
        in
        let sigelt =
            if is_flex tp.lhs
            then (match find_user_tac_for_uvar env (flex_uvar_head tp.lhs) with
              | None -> if is_flex tp.rhs then find_user_tac_for_uvar env (flex_uvar_head tp.rhs) else None
              | v -> v)
            else if is_flex tp.rhs
            then find_user_tac_for_uvar env (flex_uvar_head tp.rhs)
            else None
        in
        begin
        match sigelt with
        | None ->
          //it shouldn't have been deferred
          failwith "Impossible: No tactic associated with deferred problem"
        | Some se -> imp, se
        end
      | _ ->
        //only equality problems are deferred
        failwith "Unexpected problem deferred to tactic"
    in
    //Turn all the deferred problems into equality goals
    let eqs = List.map prob_as_implicit g.deferred_to_tac in
    //Also take any unsolved uvars in the guard implicits that are tagged
    //with attributes
    let more, imps =
        List.fold_right
            (fun imp (more, imps) ->
               match Unionfind.find imp.imp_uvar.ctx_uvar_head with
               | Some _ -> //aleady solved
                 more, imp::imps
               | None ->
                 let se = find_user_tac_for_uvar env imp.imp_uvar in
                 match se with
                 | None -> //no tac for this one
                   more, imp::imps
                 | Some se ->
                   (imp, se)::more, imps)
            g.implicits
            ([], [])
    in
    (** Each implicit is associated with a sigelt.
        Group them so that all implicits with the same associated sigelt
        are in the same bucket *)
    let bucketize (is:list (implicit * sigelt)) : list (implicits * sigelt) =
      let map : BU.smap (implicits * sigelt) = BU.smap_create 17 in
      List.iter
        (fun (i, s) ->
           match U.lid_of_sigelt s with
           | None -> failwith "Unexpected: tactic without a name"
           | Some l ->
             let lstr = Ident.string_of_lid l in
             match BU.smap_try_find map lstr with
             | None -> BU.smap_add map lstr ([i], s)
             | Some (is, s) ->
               BU.smap_remove map lstr;
               BU.smap_add map lstr (i::is, s))
        is;
        BU.smap_fold map (fun _ is out -> is::out) []
    in
    let buckets = bucketize (eqs@more) in
    // Dispatch each bucket of implicits to their respective tactic
    List.iter (fun (imps, sigel) -> solve_goals_with_tac env g imps sigel) buckets;
    { g with deferred_to_tac=[]; implicits = imps}

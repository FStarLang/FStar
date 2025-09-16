(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.SMTEncoding.SolverState
open FStarC.Effect
open FStarC
open FStarC.SMTEncoding.Term
open FStarC.BaseTypes
open FStar.List.Tot
open FStarC.Class.Show
open FStarC.Class.Setlike
module BU = FStarC.Util
module Pruning = FStarC.SMTEncoding.Pruning
module U = FStarC.SMTEncoding.UnsatCore
module TcEnv = FStarC.TypeChecker.Env

let decl_name_set = PSMap.t bool
let empty_decl_names = PSMap.empty #bool ()
let decl_names_contains (x:string) (s:decl_name_set) = Some? (PSMap.try_find s x)
let add_name (x:string) (s:decl_name_set) = PSMap.add s x true

type decls_at_level = {
  pruning_state: Pruning.pruning_state; (* the context pruning state representing all declarations visible at this level and prior levels *)
  given_decl_names: decl_name_set; (* all declarations that have been given to the solver at this level *)
  all_decls_at_level_rev: list (list decl); (* all decls at this level; in reverse order of pushes *)
  given_some_decls: bool; (* Have some declarations been flushed at this level? If not, we can pop this level without needing to flush pop to the solver *)
  to_flush_rev: list (list decl); (* declarations to be given to the solver at the next flush, in reverse order, though each nested list is in order *)
  named_assumptions: PSMap.t assumption; (* A map from assumption names to assumptions, accumulating all assumptions up to this level *)
  pruning_roots:option (list decl); (* When starting a query context, we register the declarations to be used as roots for context pruning *)
}

let init_given_decls_at_level = { 
  given_decl_names = empty_decl_names;
  all_decls_at_level_rev = [];
  pruning_state=Pruning.init;
  given_some_decls=false;
  to_flush_rev=[];
  named_assumptions = PSMap.empty ();
  pruning_roots=None
}

type solver_state = {
  levels: list decls_at_level; (* a stack of levels *)
  pending_flushes_rev: list decl; (* any declarations to be flushed before flushing the levels, typically a sequence of pops *)
  using_facts_from:option using_facts_from_setting; (* The current setting for using_facts_from *)
  retain_assumptions: decl_name_set; (* For using_facts_from: some declarations are of the form RetainAssumptions [a1; a2; ...; an]; this records their names *)
}

let depth (s:solver_state) = List.length s.levels

(* For debugging: print the solver state *)
let solver_state_to_string (s:solver_state) =
  let levels =
    List.map 
      (fun level ->
        Format.fmt3 "Level { all_decls=%s; given_decls=%s; to_flush=%s }"
          (show <| List.length level.all_decls_at_level_rev)
          (show level.given_some_decls)
          (show <| List.length level.to_flush_rev))
      s.levels
  in
  Format.fmt2 "Solver state { levels=%s; pending_flushes=%s }"
    (show levels)
    (show <| List.length s.pending_flushes_rev)

instance showable_solver_state : showable solver_state = { show = solver_state_to_string }

let debug (msg:string) (s0 s1:solver_state) =
  if Options.Ext.enabled "debug_solver_state"
  then (
    Format.print3 "Debug (%s):{\n\t before=%s\n\t after=%s\n}" msg
      (solver_state_to_string s0)
      (solver_state_to_string s1)
  )

let peek (s:solver_state) =
  match s.levels with
  | [] -> failwith "Solver state cannot have an empty stack"
  | hd::tl -> hd, tl

let replace_head (hd:decls_at_level) (s:solver_state) = { s with levels = hd :: List.tl s.levels }

let init (_:unit)
: solver_state
= { levels = [init_given_decls_at_level];
    pending_flushes_rev = [];
    using_facts_from = Some (Options.using_facts_from());
    retain_assumptions = empty_decl_names }

let push (s:solver_state)
: solver_state
= let hd, _ = peek s in
  let push = Push (List.length s.levels) in
  let next = { given_decl_names = hd.given_decl_names; 
               all_decls_at_level_rev = [];
               pruning_state = hd.pruning_state;
               given_some_decls=false;
               to_flush_rev=[[push]]; (* push a new context to the solver *)
               named_assumptions = hd.named_assumptions;
               pruning_roots=None
              } in
  { s with levels=next::s.levels }
  
let pop (s:solver_state)
: solver_state
= let hd, tl = peek s in
  if Nil? tl then failwith "Solver state cannot have an empty stack";
  let s1 =
    if not hd.given_some_decls //nothing has been given yet at this level
    then { s with levels = tl } //so we don't actually have to send a pop
    else { s with levels = tl; pending_flushes_rev = Pop (List.length tl) :: s.pending_flushes_rev }
  in
  s1
  
(* filter ds according to the using_facts_from setting:

   -- This function takes specific fields of the csolver state, rather
      than the entire solver state, as it is used as a helper in constructing a
      new solver state from a prior one, and some of its arguments are from a
      partially new solver state
*)
let filter_using_facts_from
      (using_facts_from:option using_facts_from_setting)
      (named_assumptions:PSMap.t assumption)
      (retain_assumptions:decl_name_set)
      (already_given_decl: string -> bool)
      (ds:list decl) //flattened decls
: list decl
= match using_facts_from with
  | None
  | Some [[], true] -> ds
  | Some using_facts_from ->
    let keep_assumption (a:assumption)
    : bool
    = match a.assumption_fact_ids with
      | [] -> true //retaining `a` because it is not tagged with a fact id
      | _ ->
        // the assumption is either tagged in a prior RetainAssumptions decl
        decl_names_contains a.assumption_name retain_assumptions ||
        // Or, it is enabled by the using_facts_from setting
        a.assumption_fact_ids 
        |> BU.for_some (function Name lid -> TcEnv.should_enc_lid using_facts_from lid | _ -> false)
    in
    let already_given_map : SMap.t bool = SMap.create 1000 in
    let add_assumption a = SMap.add already_given_map a.assumption_name true in
    let already_given (a:assumption)
    : bool
    = Some? (SMap.try_find already_given_map a.assumption_name) ||
      already_given_decl a.assumption_name
    in
    let map_decl (d:decl)
    : list decl
    = match d with
      | Assume a -> (
        if keep_assumption a && not (already_given a)
        then (add_assumption a; [d])
        else []
      )
      | _ ->
        [d]
    in
    let ds' = List.collect map_decl ds in
    if Options.Ext.get "debug_using_facts_from" <> ""
    then (
      let orig_n = List.length ds in
      let new_n = List.length ds' in
      if orig_n <> new_n
      then (
        Format.print4
          "Pruned using facts from:\n\t\
            Original (%s): [%s];\n\t\
            Pruned (%s): [%s]\n"
          (show orig_n)
          (show (List.map decl_to_string_short ds))
          (show new_n)
          (show (List.map decl_to_string_short ds'))
      )
    );
    ds'

let already_given_decl (s:solver_state) (aname:string)
: bool
= s.levels |> BU.for_some (fun level -> decl_names_contains aname level.given_decl_names)

let rec flatten (d:decl) : list decl = 
  match d with
  | Module (_, ds) -> List.collect flatten ds
  | _ -> [d]

(* Record assumptions with their names *)
let add_named_assumptions (named_assumptions:PSMap.t assumption) (ds:list decl)
: PSMap.t assumption
= List.fold_left
    (fun named_assumptions d ->
      match d with
      | Assume a -> PSMap.add named_assumptions a.assumption_name a
      | _ -> named_assumptions)
    named_assumptions
    ds

(* Record all names that are named in a RetainAssumptions *)
let add_retain_assumptions (ds:list decl) (s:solver_state)
: solver_state
= let ra =
    List.fold_left
      (fun ra d ->
        match d with
        | RetainAssumptions names -> 
          List.fold_left
            (fun ra name -> add_name name ra)
            ra names
        | _ -> ra)
      s.retain_assumptions
      ds
  in
  { s with retain_assumptions = ra }

(*
  The main `give` API has two modes:
  `give_delay_assumptions` is used when context_pruning is enabled, and
  `give_now` is used otherwise.

  In both cases, we have the following parameters:

    - resetting: Is this being called during a reset? If so, we don't need to
      update the pruning state---repeatedly building the pruning state on each
      reset is expensive and quadratic in the number of declarations loaded so
      far.
    - ds: The declarations to give to the solver
    - s: The current solver state
*)

(* give_delay_assumptions:
  
  This updates the top-level of the solver state, and flushes *only* the
  non-assumption declarations to the solver.

  The assumptions are retained and a selection of them may be flushed to the
  solver later, for a given set of roots of a query.
 *)
let give_delay_assumptions (resetting:bool) (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, rest = List.partition Assume? decls in
  let hd, tl = peek s in
  let hd = { hd with all_decls_at_level_rev = ds::hd.all_decls_at_level_rev;
                     to_flush_rev = rest :: hd.to_flush_rev } in
  if resetting
  then { s with levels = hd :: tl }
  else (
    let hd = 
      { hd with
        pruning_state = Pruning.add_decls decls hd.pruning_state;
        named_assumptions = add_named_assumptions hd.named_assumptions assumptions }
    in
    add_retain_assumptions decls { s with levels = hd :: tl }
  )

(* give_now:

  This updates the top-level of the solver state, and flushes *all* 
  declarations to the solver, after filtering them according to the
  using_facts_from setting
*)
let give_now (resetting:bool) (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, _ = List.partition Assume? decls in
  let hd, tl = peek s in
  let named_assumptions =
    if resetting
    then hd.named_assumptions
    else add_named_assumptions hd.named_assumptions assumptions
  in
  let ds_to_flush =
    filter_using_facts_from
      s.using_facts_from
      named_assumptions
      s.retain_assumptions
      (already_given_decl s)
      decls
  in
  let given =
    List.fold_left 
      (fun given d ->
        match d with
        | Assume a -> add_name a.assumption_name given
        | _ -> given)
      hd.given_decl_names
      ds_to_flush
  in
  let hd =
    { hd with
      given_decl_names = given;
      all_decls_at_level_rev = ds :: hd.all_decls_at_level_rev;
      to_flush_rev = ds_to_flush :: hd.to_flush_rev; }
  in
  if resetting
  then { s with levels = hd :: tl }
  else (
    let hd =
      { hd with
        pruning_state = Pruning.add_decls decls hd.pruning_state;
        named_assumptions }
    in
    add_retain_assumptions decls { s with levels = hd :: tl }
  )

let give_aux resetting (ds:list decl) (s:solver_state)
: solver_state
= if Options.Ext.enabled "context_pruning"
  then give_delay_assumptions resetting ds s
  else give_now resetting ds s

(* give: The main API for giving declarations to the solver *)
let give = give_aux false 

(* reset:
   
   This functions essentially runs the sequence of push/give operations that
   have been run so far from the init state, producing the declarations
   that should be flushed to the solver from a clean state, while considering
   the current option settings.

   E.g., if the value of context_pruning has changed, this will restore the solver
   to a state where the new setting is in effect.

*)
let reset (using_facts_from:option using_facts_from_setting) (s:solver_state)
: solver_state
= let s_new = init () in
  let s_new = { s_new with using_facts_from; retain_assumptions = s.retain_assumptions } in
  let set_pruning_roots level s = 
    let hd,tl = peek s in
    let hd = { hd with pruning_roots = level.pruning_roots } in
    { s with levels = hd :: tl }
  in
  let rebuild_level now level s_new =
    //Rebuild the level from s in the top-most level of the new solver state s_new
    let hd, tl = peek s_new in
    //1. replace the head of s_new recordingt the pruning state etc. from level
    let hd = {hd with pruning_state=level.pruning_state; named_assumptions=level.named_assumptions} in
    let s_new = { s_new with levels = hd :: tl } in
    //2. Then give all declarations at this level
    //     The `now` flag is set for levels that "follow" a level
    //     whose pruning roots have been set, i.e., for the query itself
    //   Otherwise, we give the declarations either now or delayed, depending on the current value of context_pruning
    let s = List.fold_right (if now then give_now true else give_aux true) level.all_decls_at_level_rev s_new in
    // 3. If there are pruning roots at this level, set them
    set_pruning_roots level s,
    Some? level.pruning_roots
  in
  let rec rebuild levels s_new =
    match levels with
    | [ last ] ->
      rebuild_level false last s_new
    | level :: levels ->
      //rebuild prior levels
      let s_new, now = rebuild levels s_new in
      //push a context
      let s_new = push s_new in
      //rebuild the level
      rebuild_level now level s_new
  in
  fst <| rebuild s.levels s_new
      

let name_of_assumption (d:decl) =
  match d with
  | Assume a -> a.assumption_name
  | _ -> failwith "Expected an assumption"

(* Prune the context with respect to a set of roots *)
let prune_level (roots:list decl) (hd:decls_at_level) (s:solver_state)
: decls_at_level
= // to_give is the set of assumptions reachable from roots
  let to_give = Pruning.prune hd.pruning_state roots in
  // Remove any assumptions that have already been given to the solver
  // and update the set of given declarations
  let given_decl_names, can_give = 
    List.fold_left 
      (fun (decl_name_set, can_give) to_give ->
        let name = name_of_assumption to_give in
        if not (decl_names_contains name decl_name_set)
        then (
          add_name name decl_name_set,
          to_give::can_give
        )
        else decl_name_set, can_give)
      (hd.given_decl_names, [])
      to_give
  in
  // Filter the assumptions that can be given to the solver
  // according to the using_facts_from setting
  let can_give =
    filter_using_facts_from
      s.using_facts_from
      hd.named_assumptions
      s.retain_assumptions
      (already_given_decl s)
      can_give
  in
  let hd = { hd with given_decl_names;
                     to_flush_rev = can_give::hd.to_flush_rev } in
  hd

(* Run pruning in a "simulation" mode, where we don't actually prune the context,
   but instead return the names of the assumptions that would have been pruned. *)
let prune_sim (roots:list decl) (s:solver_state)
: list string
= let hd, tl = peek s in
  let to_give = Pruning.prune hd.pruning_state roots in
  let can_give =
    filter_using_facts_from
      s.using_facts_from
      hd.named_assumptions
      s.retain_assumptions
      (already_given_decl s)
      to_give
  in
  List.map name_of_assumption (List.filter Assume? roots@can_give)

(* Start a query context, registering and pushing the roots *)
let start_query (msg:string) (roots_to_push:list decl) (qry:decl) (s:solver_state)
: solver_state
= let hd, tl = peek s in
  let s = { s with levels = { hd with pruning_roots = Some (qry::roots_to_push) } :: tl } in
  let s = push s in
  let s = give [Caption msg] s in
  give_now false roots_to_push s

(* Finising a query context, popping and clearing the roots *)
let finish_query (msg:string) (s:solver_state)
: solver_state
= let s = give [Caption msg] s in
  let s = pop s in
  let hd, tl = peek s in
  { s with levels = { hd with pruning_roots = None } :: tl }

(* Filter all declarations visible with an unsat core *)
let filter_with_unsat_core queryid (core:U.unsat_core) (s:solver_state) 
: list decl
= let rec all_decls levels = 
    match levels with
    | [last] -> last.all_decls_at_level_rev
    | level :: levels -> 
      level.all_decls_at_level_rev@[Push <| List.length levels]::all_decls levels
  in
  let all_decls = all_decls s.levels in
  let all_decls = List.flatten <| List.rev all_decls in
  U.filter core all_decls

let would_have_pruned (s:solver_state) =
  if not (Options.Ext.enabled "context_pruning_sim")
  then None
  else 
    (*find the first level with pruning roots, and prune the context with respect to them *)
    let rec aux levels =
      match levels with
      | [] -> None
      | level :: levels ->
        match level.pruning_roots with
        | Some roots -> 
          Some (prune_sim roots s)
        | None -> aux levels 
    in
    aux s.levels

(* flush: Emit declarations to the solver *)
let flush (s:solver_state)
: list decl & solver_state
= let s =
    if Options.Ext.enabled "context_pruning"
    then (
      (*find the first level with pruning roots, and prune the context with respect to them *)
      let rec aux levels =
        match levels with
        | [] -> []
        | level :: levels ->
          match level.pruning_roots with
          | Some roots -> 
            let hd = prune_level roots level s in
            hd :: levels
          | None -> 
            level :: aux levels 
      in
      { s with levels = aux s.levels }
    )
    else s
  in
  (* Gather all decls to be flushd per level *)
  let to_flush = 
    List.flatten <|
    List.rev <|
    List.collect (fun level -> level.to_flush_rev) s.levels 
  in
  (* Update the solver state, clearing the pending flushes per level and recording that some decls were flushed *)
  let levels =
    List.map
      (fun level -> { level with
                      given_some_decls=(level.given_some_decls || Cons? level.to_flush_rev);
                      to_flush_rev = [] })
      s.levels
  in
  let s1 = { s with levels; pending_flushes_rev=[] } in
  (* prefix any pending flushes to the list of decls to be flushed *)
  let flushed = List.rev s.pending_flushes_rev @ to_flush in
  flushed,
  s1

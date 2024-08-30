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
module FStar.SMTEncoding.SolverState
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Compiler.Util
open FStar.List.Tot
open FStar.Class.Show
module BU = FStar.Compiler.Util
module Pruning = FStar.SMTEncoding.Pruning
module U = FStar.SMTEncoding.UnsatCore
module TcEnv = FStar.TypeChecker.Env

let decl_name_set = BU.psmap bool
let empty_decl_names = BU.psmap_empty #bool ()
let decl_names_contains (x:string) (s:decl_name_set) = Some? (BU.psmap_try_find s x)
let add_name (x:string) (s:decl_name_set) = BU.psmap_add s x true
type decls_at_level = {
  pruning_state: Pruning.pruning_state;
  given_decl_names: decl_name_set;
  all_decls_at_level_rev: list (list decl); (* all decls at this level; in reverse order of pushes *)
  given_some_decls: bool; //list (list decl); (* all declarations that have been flushed so far; in reverse order *)
  to_flush_rev: list (list decl); (* declarations to be given to the solver at the next flush, in reverse order, though each nested list is in order *)
  named_assumptions: BU.psmap assumption;
  pruning_roots:option (list decl)
}

let init_given_decls_at_level = { 
  given_decl_names = empty_decl_names;
  all_decls_at_level_rev = [];
  pruning_state=Pruning.init;
  given_some_decls=false;
  to_flush_rev=[];
  named_assumptions = BU.psmap_empty ();
  pruning_roots=None
}

type solver_state = {
  levels: list decls_at_level;
  pending_flushes_rev: list decl;
  using_facts_from:option using_facts_from_setting;
  prune_sim:option (list string)
}

let depth (s:solver_state) = List.length s.levels

let solver_state_to_string (s:solver_state) =
  let levels =
    List.map 
      (fun level ->
        BU.format3 "Level { all_decls=%s; given_decls=%s; to_flush=%s }"
          (show <| List.length level.all_decls_at_level_rev)
          (show level.given_some_decls)
          (show <| List.length level.to_flush_rev))
      s.levels
  in
  BU.format2 "Solver state { levels=%s; pending_flushes=%s }"
    (show levels)
    (show <| List.length s.pending_flushes_rev)

instance showable_solver_state : showable solver_state = { show = solver_state_to_string }

let debug (msg:string) (s0 s1:solver_state) =
  if Options.Ext.get "debug_solver_state" <> ""
  then (
    BU.print3 "Debug (%s):{\n\t before=%s\n\t after=%s\n}" msg
      (solver_state_to_string s0)
      (solver_state_to_string s1)
  )

let peek (s:solver_state) =
  match s.levels with
  | [] -> failwith "Solver state cannot have an empty stack"
  | hd::tl -> hd, tl

let init (_:unit)
: solver_state
= { levels = [init_given_decls_at_level];
    pending_flushes_rev = [];
    using_facts_from = Some (Options.using_facts_from());
    prune_sim = None }

let push (s:solver_state)
: solver_state
= let hd, _ = peek s in
  let push = Push (List.length s.levels) in
  let next = { given_decl_names = hd.given_decl_names; 
               all_decls_at_level_rev = [];
               pruning_state = hd.pruning_state;
               given_some_decls=false;
               to_flush_rev=[[push]];
               named_assumptions = hd.named_assumptions;
               pruning_roots=None
              } in
  let s1 = 
    { s with
      levels=next::s.levels;
    }
  in
  s1
  

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
  
let filter_using_facts_from
      (using_facts_from:option using_facts_from_setting)
      (named_assumptions:BU.psmap assumption)
      (s:solver_state)
      (ds:list decl) //flattened decls
: list decl
= if Options.Ext.get "disregard_using_facts_from" <> "" then ds else
  match using_facts_from with
  | None
  | Some [[], true] -> ds
  | Some using_facts_from ->
    let keep_assumption (a:assumption)
    : bool
    = match a.assumption_fact_ids with
      | [] -> true //retaining `a` because it is not tagged with a fact id
      | _ ->
        a.assumption_fact_ids 
        |> BU.for_some (function Name lid -> TcEnv.should_enc_lid using_facts_from lid | _ -> false)
    in
    let already_given_map : BU.smap bool = BU.smap_create 1000 in
    let add_assumption a = BU.smap_add already_given_map a.assumption_name true in
    let already_given (a:assumption)
    : bool
    = Some? (BU.smap_try_find already_given_map a.assumption_name) ||
      s.levels |> BU.for_some (fun level -> decl_names_contains a.assumption_name level.given_decl_names)
    in
    let map_decl (d:decl)
    : list decl
    = match d with
      | Assume a -> (
        if keep_assumption a && not (already_given a)
        then (add_assumption a; [d])
        else []
      )
      | RetainAssumptions names ->
        let assumptions = 
          names |>
          List.collect (fun name ->
            match BU.psmap_try_find named_assumptions name with
            | None -> []
            | Some a ->
              if already_given a then [] else (add_assumption a; [Assume a]))
        in
        assumptions
      | _ ->
        [d]
    in
    let ds = List.collect map_decl ds in
    ds



// let reset (using_facts_from:option using_facts_from_setting) (s:solver_state) =
//   let to_flush, levels =
//     List.fold_right
//       (fun level (to_flush, levels) ->
//         let level = 
//           { level with
//             to_flush_rev=[];
//             given_decls_rev=level.to_flush_rev@level.given_decls_rev} in
//         to_flush@List.rev level.given_decls_rev,
//         level::levels)
//       s.levels ([], [])
//   in
//   let using_facts_from = match using_facts_from with
//     | Some u -> Some u
//     | None -> s.using_facts_from in
//   let s1 = { s with using_facts_from; levels; pending_flushes_rev=List.rev to_flush } in
//   debug "reset" s s1; s1

let rec flatten (d:decl) : list decl = 
  match d with
  | Module (_, ds) -> List.collect flatten ds
  | _ -> [d]

let add_named_assumptions (named_assumptions:BU.psmap assumption) (ds:list decl)
: BU.psmap assumption
= List.fold_left
    (fun named_assumptions d ->
      match d with
      | Assume a -> BU.psmap_add named_assumptions a.assumption_name a
      | _ -> named_assumptions)
    named_assumptions
    ds

let give_delay_assumptions (resetting:bool) (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, rest = List.partition Assume? decls in
  let hd, tl = peek s in
  let hd = { hd with all_decls_at_level_rev = ds::hd.all_decls_at_level_rev;
                     to_flush_rev = rest :: hd.to_flush_rev } in
  let hd = 
    if resetting
    then hd
    else { hd with
          pruning_state = Pruning.add_decls decls hd.pruning_state;
          named_assumptions = add_named_assumptions hd.named_assumptions assumptions }
  in
  { s with levels = hd :: tl }

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
  let ds_to_flush = filter_using_facts_from s.using_facts_from named_assumptions s decls in
  let given =
    List.fold_left 
      (fun given d ->
        match d with
        | Assume a -> add_name a.assumption_name given
        | _ -> given)
      hd.given_decl_names
      ds_to_flush
  in
  let hd = { hd with
    given_decl_names = given;
    all_decls_at_level_rev = ds :: hd.all_decls_at_level_rev;
    to_flush_rev = ds_to_flush :: hd.to_flush_rev;
  } in
  let hd =
    if resetting
    then hd
    else { hd with
           pruning_state = Pruning.add_decls decls hd.pruning_state;
           named_assumptions }
  in
  { s with
    levels = hd :: tl
  }

let give_aux resetting (ds:list decl) (s:solver_state)
: solver_state
= if Options.Ext.get "context_pruning" <> ""
  then give_delay_assumptions resetting ds s
  else give_now resetting ds s

let give = give_aux false 

let reset_with_new_using_facts_from (using_facts_from:option using_facts_from_setting) (s:solver_state)
: solver_state
= let s_new = init () in
  let s_new = { s_new with using_facts_from } in
  let set_pruning_roots level s = 
    let hd,tl = peek s in
    let hd = { hd with pruning_roots = level.pruning_roots } in
    { s with levels = hd :: tl }
  in
  let rebuild_level now level s_new =
    let hd, tl = peek s_new in
    let hd = {hd with pruning_state=level.pruning_state; named_assumptions=level.named_assumptions} in
    let s_new = { s_new with levels = hd :: tl } in
    let s = List.fold_right (if now then give_now true else give_aux true) level.all_decls_at_level_rev s_new in
    set_pruning_roots level s,
    Some? level.pruning_roots
  in
  let rec rebuild levels s_new =
    match levels with
    | [ last ] ->
      rebuild_level false last s_new
    | level :: levels ->
      let s_new, now = rebuild levels s_new in
      let s_new = push s_new in
      rebuild_level now level s_new
  in
  fst <| rebuild s.levels s_new
      
let reset (using_facts_from:option using_facts_from_setting) (s:solver_state) =
  let s' =
   { reset_with_new_using_facts_from using_facts_from s with
     prune_sim = s.prune_sim }
  in
  s'

let name_of_assumption (d:decl) =
  match d with
  | Assume a -> a.assumption_name
  | _ -> failwith "Expected an assumption"

let prune_level (roots:list decl) (hd:decls_at_level) (s:solver_state)
: decls_at_level
= let to_give = Pruning.prune hd.pruning_state roots in
  let decl_name_set, can_give = 
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
  let can_give = filter_using_facts_from s.using_facts_from hd.named_assumptions s can_give in
  let hd = { hd with given_decl_names = decl_name_set;
                     to_flush_rev = can_give::hd.to_flush_rev } in
  hd

let prune_sim (roots_to_push:list decl) (s:solver_state)
: list string
= let hd, tl = peek s in
  let to_give = Pruning.prune hd.pruning_state (roots_to_push) in
  List.map name_of_assumption (List.filter Assume? roots_to_push@to_give)

let start_query (msg:string) (roots_to_push:list decl) (qry:decl) (s:solver_state)
: solver_state
= let hd, tl = peek s in
  let s = { s with levels = { hd with pruning_roots = Some (qry::roots_to_push) } :: tl } in
  let s = push s in
  let s = give [Caption msg] s in
  give_now false roots_to_push s

let finish_query (msg:string) (s:solver_state)
: solver_state
= let s = give [Caption msg] s in
  let s = pop s in
  let hd, tl = peek s in
  { s with levels = { hd with pruning_roots = None } :: tl }

let would_have_pruned (s:solver_state) =
  if Options.Ext.get "context_pruning_sim" = ""
  then None
  else 
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

let filter_with_unsat_core queryid (core:U.unsat_core) (s:solver_state) 
: list decl
= let rec all_decls levels = 
    match levels with
    | [last] -> last.all_decls_at_level_rev
    | level :: levels -> 
      level.all_decls_at_level_rev@[Push <| List.length levels]::all_decls levels
  in
  let all_decls = all_decls s.levels in
// List.collect (fun level -> level.all_decls_at_level_rev) s.levels in
  let all_decls = List.flatten <| List.rev all_decls in
  U.filter core all_decls

let flush (s:solver_state)
: list decl & solver_state
= let s =
    if Options.Ext.get "context_pruning" <> ""
    // || Options.Ext.get "context_pruning_sim" <> ""
    then (
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
  let to_flush = 
    List.flatten <|
    List.rev <|
    List.collect (fun level -> level.to_flush_rev) s.levels 
  in
  //   List.fold_right
  //     (fun level out -> out @ List.rev level.to_flush_rev)
  //   s.levels []
  // in
  let levels =
    List.map
      (fun level -> { level with
                      given_some_decls=(level.given_some_decls || Cons? level.to_flush_rev);
                      to_flush_rev = [] })
      s.levels
  in
  let s1 = { s with levels; pending_flushes_rev=[] } in
  let flushed = List.rev s.pending_flushes_rev @ to_flush in
  flushed,
  s1
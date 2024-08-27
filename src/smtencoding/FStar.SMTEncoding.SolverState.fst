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
  given_decls_rev: list decl; (* all declarations that have been flushed so far *)
  to_flush_rev: list decl; (* declarations to be given to the solver at the next flush *)
  named_assumptions: BU.psmap assumption;
}

let init_given_decls_at_level = { 
  given_decl_names = empty_decl_names;
  all_decls_at_level_rev = [];
  pruning_state=Pruning.init;
  given_decls_rev=[];
  to_flush_rev=[];
  named_assumptions = BU.psmap_empty ()
}

type solver_state = {
  levels: list decls_at_level;
  pending_flushes_rev: list decl;
  using_facts_from:option using_facts_from_setting;
}

let solver_state_to_string (s:solver_state) =
  let levels =
    List.map 
      (fun level ->
        BU.format3 "Level { all_decls=%s; given_decls=%s; to_flush=%s }"
          (show <| List.length level.all_decls_at_level_rev)
          (show <| List.length level.given_decls_rev)
          (show <| List.length level.to_flush_rev))
      s.levels
  in
  BU.format2 "Solver state { levels=%s; pending_flushes=%s }"
    (show levels)
    (show <| List.length s.pending_flushes_rev)

let debug (msg:string) (s0 s1:solver_state) =
  if Options.ext_getv "debug_solver_state" <> ""
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
    using_facts_from = Some (Options.using_facts_from()) }

let push (s:solver_state)
: solver_state
= let hd, _ = peek s in
  let push = Push (List.length s.levels) in
  let next = { given_decl_names = hd.given_decl_names; 
               all_decls_at_level_rev = [];
               pruning_state = hd.pruning_state;
               given_decls_rev=[];
               to_flush_rev=[push];
               named_assumptions = hd.named_assumptions
              } in
  let s1 = 
    { s with
      levels=next::s.levels;
    }
  in
  debug "push" s s1;
  s1
  

let pop (s:solver_state)
: solver_state
= let hd, tl = peek s in
  if Nil? tl then failwith "Solver state cannot have an empty stack";
  let s1 =
    if Nil? hd.given_decls_rev //nothing has been given yet at this level
    then { s with levels = tl } //so we don't actually have to send a pop
    else { s with levels = tl; pending_flushes_rev = Pop (List.length s.levels) :: s.pending_flushes_rev }
  in
  debug "pop" s s1;
  s1
  
let filter_using_facts_from
      (using_facts_from:option using_facts_from_setting)
      (named_assumptions:BU.psmap assumption)
      (s:solver_state)
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

let give_delay_assumptions (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, rest = List.partition Assume? decls in
  let hd, tl = peek s in
  let hd = { hd with
    pruning_state = Pruning.add_assumptions assumptions hd.pruning_state;
    all_decls_at_level_rev = ds::hd.all_decls_at_level_rev;
    named_assumptions = add_named_assumptions hd.named_assumptions assumptions;
    to_flush_rev = List.rev rest @ hd.to_flush_rev
  } in
  { s with levels = hd :: tl }

let give_now (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, _ = List.partition Assume? decls in
  let hd, tl = peek s in
  let named_assumptions = add_named_assumptions hd.named_assumptions assumptions in
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
    pruning_state = Pruning.add_assumptions assumptions hd.pruning_state;
    all_decls_at_level_rev = ds :: hd.all_decls_at_level_rev;
    to_flush_rev = List.rev ds_to_flush @ hd.to_flush_rev;
    named_assumptions
  } in
  { s with
    levels = hd :: tl
  }

let give (ds:list decl) (s:solver_state)
: solver_state
= if Options.ext_getv "context_pruning" <> ""
  then give_delay_assumptions ds s
  else give_now ds s

let reset_with_new_using_facts_from (using_facts_from:option using_facts_from_setting) (s:solver_state)
: solver_state
= let s_new = init () in
  let s_new = { s_new with using_facts_from } in
  let rec rebuild_one_level (all_decls_at_level_rev:list (list decl)) s_new =
    match all_decls_at_level_rev with
    | [ last ] -> give last s_new
    | decls :: decls_l ->
      give decls (rebuild_one_level decls_l s_new)
  in
  let rec rebuild levels s_new =
    match levels with
    | [ last ] ->
      List.fold_right give last.all_decls_at_level_rev s_new
    | level :: levels ->
      let s_new = push (rebuild levels s_new) in
      List.fold_right give level.all_decls_at_level_rev s_new
  in
  rebuild s.levels s_new
      
let reset (using_facts_from:option using_facts_from_setting) (s:solver_state) =
  // if using_facts_from = s.using_facts_from
  // then (
  //   let levels =
  //     List.map
  //       (fun level -> 
  //         { level with
  //           given_decls_rev=[]; 
  //           to_flush_rev=level.to_flush_rev@level.given_decls_rev })
  //       s.levels
  //   in
  //   let s1 = { s with levels; pending_flushes_rev=[] } in
  //   debug "reset" s s1;
  //   s1
  // )
  // else 
  reset_with_new_using_facts_from using_facts_from s

let name_of_assumption (d:decl) =
  match d with
  | Assume a -> a.assumption_name
  | _ -> failwith "Expected an assumption"

let prune (roots:list decl) (s:solver_state)
: solver_state
= s
  // let hd, tl = peek s in
  // let to_give = Pruning.prune hd.pruning_state roots in
  // let decl_name_set, can_give = 
  //   List.fold_left 
  //     (fun (decl_name_set, can_give) to_give ->
  //       let name = name_of_assumption to_give in
  //       if not (decl_names_contains name decl_name_set)
  //       then (
  //         add_name name decl_name_set,
  //         to_give::can_give
  //       )
  //       else decl_name_set, can_give)
  //     (hd.given_decl_names, [])
  //     to_give
  // in
  // let hd = { hd with given_decl_names = decl_name_set } in
  // let s = { levels = hd :: tl; to_flush=can_give@s.to_flush } in
  // s

let filter_with_unsat_core (core:U.unsat_core) (s:solver_state) 
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
= let to_flush = 
    List.fold_right
      (fun level out -> out @ List.rev level.to_flush_rev)
    s.levels []
  in
  let levels =
    List.map
      (fun level -> { level with
                      given_decls_rev=level.to_flush_rev@level.given_decls_rev;
                      to_flush_rev = [] })
      s.levels
  in
  let s1 = { s with levels; pending_flushes_rev=[] } in
  debug "flush" s s1;
  if Options.ext_getv "debug_solver_state" <> ""
  then BU.print1 "Flushed %s\n" (show <| List.length to_flush);
  let flushed = List.rev s.pending_flushes_rev @ to_flush in
  flushed,
  s1
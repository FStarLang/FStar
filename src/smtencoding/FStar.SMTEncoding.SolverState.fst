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

let decl_name_set = BU.psmap bool
let empty_decl_names = BU.psmap_empty #bool ()
let decl_names_contains (x:string) (s:decl_name_set) = Some? (BU.psmap_try_find s x)
let add_name (x:string) (s:decl_name_set) = BU.psmap_add s x true
type decls_at_level = {
  pruning_state: Pruning.pruning_state;
  given_decl_names: decl_name_set;
  all_decls_at_level_rev: list decl;
  given_decls_rev: list decl;
  to_flush_rev: list decl;
}

let init_given_decls_at_level = { 
  given_decl_names = empty_decl_names;
  all_decls_at_level_rev = [];
  pruning_state=Pruning.init;
  given_decls_rev=[];
  to_flush_rev=[];
}

type solver_state = {
  levels: list decls_at_level;
  pending_flushes_rev: list decl
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
    pending_flushes_rev = [] }

let push (s:solver_state)
: solver_state
= let hd, _ = peek s in
  let next = { given_decl_names = hd.given_decl_names; 
               all_decls_at_level_rev = [];
               pruning_state = hd.pruning_state;
               given_decls_rev=[];
               to_flush_rev=[Push (List.length s.levels)]
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
    else { levels = tl; pending_flushes_rev = Pop (List.length s.levels) :: s.pending_flushes_rev }
  in
  debug "pop" s s1;
  s1
  
let reset (s:solver_state) =
  let to_flush, levels =
    List.fold_right
      (fun level (to_flush, levels) ->
        let level = 
          { level with
            to_flush_rev=[];
            given_decls_rev=level.to_flush_rev@level.given_decls_rev} in
        to_flush@List.rev level.given_decls_rev,
        level::levels)
      s.levels ([], [])
  in
  let s1 = { s with levels; pending_flushes_rev=List.rev to_flush } in
  debug "reset" s s1; s1

let rec flatten (d:decl) : list decl = 
  match d with
  | Module (_, ds) -> List.collect flatten ds
  | _ -> [d]

// let give_delay_assumptions (ds:list decl) (s:solver_state) 
// : solver_state
// = let decls = List.collect flatten ds in
//   let assumptions, rest = List.partition Assume? decls in
//   let hd, tl = peek s in
//   let hd = { hd with
//     pruning_state = Pruning.add_assumptions assumptions hd.pruning_state;
//     all_decls_at_level_rev = List.rev ds@hd.all_decls_at_level_rev;
//   } in
//   {
//     levels = hd :: tl;
//     to_flush=List.rev rest @ s.to_flush
//   }

let give_now (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, rest = List.partition Assume? decls in
  let hd, tl = peek s in
  let given =
    List.fold_left 
      (fun given d ->
        match d with
        | Assume a -> add_name a.assumption_name given)
      hd.given_decl_names
      assumptions
  in
  let hd = { hd with
    given_decl_names = given;
    pruning_state = Pruning.add_assumptions assumptions hd.pruning_state;
    all_decls_at_level_rev = List.rev ds@hd.all_decls_at_level_rev;
    to_flush_rev = List.rev ds @ hd.to_flush_rev;
  } in
  { s with
    levels = hd :: tl
  }

let give (ds:list decl) (s:solver_state)
: solver_state
= 
  // if Options.ext_getv "context_pruning" <> ""
  // then give_delay_assumptions ds s
  // else
  let s1 = give_now ds s in
  debug "give" s s1; s1

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
= let all_decls =
    List.fold_right
      (fun level out -> out@List.rev level.all_decls_at_level_rev)
      s.levels []
  in
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
  let s1 = { levels; pending_flushes_rev=[] } in
  debug "flush" s s1;
  if Options.ext_getv "debug_solver_state" <> ""
  then BU.print1 "Flushed %s\n" (show <| List.length to_flush);
  let flushed = List.rev s.pending_flushes_rev @ to_flush in
  flushed,
  s1
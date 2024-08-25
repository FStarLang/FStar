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
module BU = FStar.Compiler.Util
module Pruning = FStar.SMTEncoding.Pruning

let decl_name_set = BU.psmap bool
let empty_decl_names = BU.psmap_empty #bool ()
let decl_names_contains (x:string) (s:decl_name_set) = Some? (BU.psmap_try_find s x)
let add_name (x:string) (s:decl_name_set) = BU.psmap_add s x true
type decls_at_level = {
  given_decl_names: decl_name_set;
  all_decls_at_level: list decl;
  pruning_state: Pruning.pruning_state;
  given_decls: list decl
}

let init_given_decls_at_level = { 
  given_decl_names = empty_decl_names;
  all_decls_at_level = [];
  pruning_state=Pruning.init;
  given_decls=[]
}

type solver_state = {
  levels: list decls_at_level;
  to_flush: list decl
}

let peek (s:solver_state) =
  match s.levels with
  | [] -> failwith "Solver state cannot have an empty stack"
  | hd::tl -> hd, tl

let init (_:unit)
: solver_state
= { levels = [init_given_decls_at_level];
    to_flush = [] }

let push (s:solver_state)
: solver_state
= let hd, _ = peek s in
  let next = { given_decl_names = hd.given_decl_names; 
               all_decls_at_level = [];
               pruning_state = hd.pruning_state;
               given_decls=[] } in
  { 
    levels=next::s.levels;
    to_flush = Push (List.length s.levels) :: s.to_flush
  }

let pop (s:solver_state)
: solver_state
= let _, tl = peek s in
  if Nil? tl then failwith "Solver state cannot have an empty stack";
  {
    levels = tl;
    to_flush = Pop (List.length tl) :: s.to_flush
  }

let reset (s:solver_state) =
  let to_flush =
    List.fold_right
      (fun level out -> out@level.given_decls)
      s.levels []
  in
  { s with to_flush=List.rev to_flush }


let rec flatten (d:decl) : list decl = 
  match d with
  | Module (_, ds) -> List.collect flatten ds
  | _ -> [d]

let give_delay_assumptions (ds:list decl) (s:solver_state) 
: solver_state
= let decls = List.collect flatten ds in
  let assumptions, rest = List.partition Assume? decls in
  let hd, tl = peek s in
  let hd = { hd with
    pruning_state = Pruning.add_assumptions assumptions hd.pruning_state;
    all_decls_at_level = List.rev ds@hd.all_decls_at_level;
  } in
  {
    levels = hd :: tl;
    to_flush=List.rev rest @ s.to_flush
  }

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
    all_decls_at_level = List.rev ds@hd.all_decls_at_level;
    given_decls = hd.given_decls @ ds
  } in
  {
    levels = hd :: tl;
    to_flush=List.rev ds @ s.to_flush
  }

let give (ds:list decl) (s:solver_state)
: solver_state
= if Options.ext_getv "context_pruning" <> ""
  then give_delay_assumptions ds s
  else give_now ds s

let name_of_assumption (d:decl) =
  match d with
  | Assume a -> a.assumption_name
  | _ -> failwith "Expected an assumption"

let prune (roots:list decl) (s:solver_state)
: solver_state
= let hd, tl = peek s in
  let to_give = Pruning.prune hd.pruning_state roots in
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
  let hd = { hd with given_decl_names = decl_name_set } in
  let s = { levels = hd :: tl; to_flush=can_give@s.to_flush } in
  s

let flush (s:solver_state)
: list decl & solver_state
= List.rev s.to_flush, { s with to_flush = []}

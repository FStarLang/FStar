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
module FStarC.SMTEncoding.UnsatCore
open FStarC.Effect
open FStarC
open FStarC.SMTEncoding.Term
module BU = FStarC.Util

let filter (core:unsat_core) (decls:list decl)
: list decl
= let rec aux theory =
    //so that we can use the tail-recursive fold_left
    let theory_rev = List.rev theory in
    let keep, n_retained, n_pruned =
        List.fold_left 
        (fun (keep, n_retained, n_pruned) d ->
          match d with
          | Assume a ->
              if List.contains a.assumption_name core
              then d::keep, n_retained+1, n_pruned
              else if BU.starts_with a.assumption_name "@"
              then d::keep, n_retained, n_pruned
              else keep, n_retained, n_pruned+1
          | Module (name, decls) ->
              let keep', n, m = aux decls in
              Module(name, keep')::keep, n_retained + n, n_pruned + m
          | _ -> d::keep, n_retained, n_pruned)
        ([Caption ("UNSAT CORE USED: " ^ (core |> String.concat ", "))],//start with the unsat core caption at the end
        0,
        0)
        theory_rev
    in
    keep, n_retained, n_pruned
  in
  let keep, _, _ = aux decls in
  keep

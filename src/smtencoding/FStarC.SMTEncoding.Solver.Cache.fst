(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

module FStarC.SMTEncoding.Solver.Cache

open FStarC
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax

open FStarC.RBSet

open FStarC.Class.Show
open FStarC.Class.Hashable
open FStarC.Syntax.Hash {} // instances

let query_cache_ref : ref (RBSet.t hash_code) =
  mk_ref (empty ())

let on () =
  Options.query_cache () && Options.ide ()

let query_cache_add (g:env) (q:term) : unit =
  if on () then (
    let h = hash (g, q) in
//     Format.print1 "Adding query cache for %s\n" (show h);
    query_cache_ref := add h !query_cache_ref
  )

let try_find_query_cache (g:env) (q:term) : bool =
  if on () then (
    let h = hash (g, q) in
    let r = mem h !query_cache_ref in
//     Format.print2 "Looked up query cache for %s, r = %s\n" (show h) (show r);
    r
  ) else
    false

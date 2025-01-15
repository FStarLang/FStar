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
module FStarC.Tests.Data
// tests about data structures


open FStar open FStarC
open FStarC
open FStarC.Effect
module BU = FStarC.Util

module FlatSet = FStarC.FlatSet
module RBSet = FStarC.RBSet

open FStarC.Class.Setlike
open FStarC.Class.Show

let rec insert (n:int) {| setlike int 'set |} (s : 'set)  =
  if n = 0 then s
  else insert (n-1) (add n s)

let rec all_mem (n:int) {| setlike int 'set |} (s : 'set) =
  if n = 0 then true
  else mem n s && all_mem (n-1) s

let rec all_remove (n:int) {| setlike int 'set |} (s : 'set) =
  if n = 0 then s
  else all_remove (n-1) (remove n s)

let nn = 10000

let run_all () =
  BU.print_string "data tests\n";
  let (f, ms) = BU.record_time_ms (fun () -> insert nn (empty () <: FlatSet.t int)) in
  BU.print1 "FlatSet insert: %s\n" (show ms);
  let (f_ok, ms) = BU.record_time_ms (fun () -> all_mem nn f) in
  BU.print1 "FlatSet all_mem: %s\n" (show ms);
  let (f, ms) = BU.record_time_ms (fun () -> all_remove nn f) in
  BU.print1 "FlatSet all_remove: %s\n" (show ms);

  if not f_ok then failwith "FlatSet all_mem failed";
  if not (is_empty f) then failwith "FlatSet all_remove failed";

  let (rb, ms) = BU.record_time_ms (fun () -> insert nn (empty () <: RBSet.t int)) in
  BU.print1 "RBSet insert: %s\n" (show ms);
  let (rb_ok, ms) = BU.record_time_ms (fun () -> all_mem nn rb) in
  BU.print1 "RBSet all_mem: %s\n" (show ms);
  let (rb, ms) = BU.record_time_ms (fun () -> all_remove nn rb) in
  BU.print1 "RBSet all_remove: %s\n" (show ms);

  if not rb_ok then failwith "RBSet all_mem failed";
  if not (is_empty rb) then failwith "RBSet all_remove failed";
  ()

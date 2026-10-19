(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Timing

open FStarC.Effect

[@@custard_extern "int64"]
private assume new type ocaml_int64 : Type0

type time_ns = ocaml_int64

[@@custard_extern "Mtime_clock.now_ns"]
let now_ns _ = admit ()

[@@custard_extern "(fun t1 t2 -> Z.of_int (Int64.to_int (Int64.sub t2 t1)))"]
private assume val diff : time_ns -> time_ns -> int

let diff_ms t1 t2 = diff t1 t2 / 1000000

let diff_ns t1 t2 = diff t1 t2

let record_ns f =
  let start = now_ns () in
  let res = f () in
  res, diff_ns start (now_ns ())

let record_ms f =
  let res, ns = record_ns f in
  res, ns / 1000000

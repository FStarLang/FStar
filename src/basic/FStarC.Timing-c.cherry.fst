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

(* The Cherry implementation: nanoseconds of the monotonic clock. *)

open FStarC.Effect
module U64 = FStar.UInt64

type time_ns = U64.t

(* clock_gettime (CLOCK_MONOTONIC), in ulib/c/cherry.c. *)
[@@custard_extern "cherry_now_ns"]
private assume val clock_ns : unit -> ML U64.t

let now_ns () = clock_ns ()

let diff_ms t1 t2 = (U64.v t2 - U64.v t1) / 1000000

let diff_ns t1 t2 = U64.v t2 - U64.v t1

[@@FStar.Attributes.custard_inline]
let record_ns f =
  let start = now_ns () in
  let res = f () in
  res, diff_ns start (now_ns ())

[@@FStar.Attributes.custard_inline]
let record_ms f =
  let start = now_ns () in
  let res = f () in
  res, diff_ms start (now_ns ())

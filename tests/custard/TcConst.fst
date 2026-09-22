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

(* Section 76.  A type class with a value method, which used to cost a
   run-time initializer per instance and per reader.

   [start] is a named constant, so the instance field is initialized from
   another global rather than from a literal -- which is the shape the report
   named ([foo_bar__t = UInt32_zero;]), and the one C refuses as an
   initializer.  [bumped] and [twice] read the method and compute, so the
   chain is three deep and the last link is arithmetic and not a copy.

   The assertion is that [custard_init_globals] is not generated at all: with
   nothing left for it to set, the interface does not declare it and [main]
   does not call it.  The values still have to be right, so the program checks
   its own answer. *)
module TcConst
module U32 = FStar.UInt32
module U8 = FStar.UInt8

class foo (t: Type0) = { bar: U32.t; small: U8.t }

let start : U32.t = 7ul

instance foo_u32 : foo U32.t = { bar = start; small = 200uy }

let bumped (#t:Type0) {| foo t |} : U32.t = U32.add_mod (bar #t #_) 1ul

let twice (#t:Type0) {| foo t |} : U32.t = U32.mul_mod (bumped #t #_) 2ul

(* A narrow width, so that the folded initializer has to carry the same
   truncation the run-time assignment would have: 200 + 100 is 300 at [int],
   and [uint8_t] holds 44. *)
let wrapped (#t:Type0) {| foo t |} : U8.t = U8.add_mod (small #t #_) 100uy

let main () : FStar.All.ML FStar.Int32.t =
  if U32.eq (twice #U32.t #foo_u32) 16ul && U8.eq (wrapped #U32.t #foo_u32) 44uy
  then 0l else 1l

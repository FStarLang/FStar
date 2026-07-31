(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Range

(* The user-facing FStar.Range module is realized by the compiler's own range
   type, so that [range] denotes the same (unsealed) type everywhere. This is
   the F* replacement for the hand-written ulib/ml/plugin/FStar_Range.ml.

   We [friend] FStarC.Range.Type so we can (a) see that the range type is a
   plain record, hence an [eqtype], and (b) implement [join_range]/[explode] as
   total functions (the FStarC.Range.Ops versions are in the ML effect via the
   Ord typeclass). *)

friend FStarC.Range.Type
module T = FStarC.Range.Type

let range = T.range

let range_0 = T.dummyRange

let mk_range file from_line from_col to_line to_col =
  T.mk_range file (T.mk_pos from_line from_col) (T.mk_pos to_line to_col)

let pos_leq (p1 p2 : T.pos) : bool =
  p1.line < p2.line || (p1.line = p2.line && p1.col <= p2.col)

let min_pos (p1 p2 : T.pos) : T.pos = if pos_leq p1 p2 then p1 else p2
let max_pos (p1 p2 : T.pos) : T.pos = if pos_leq p1 p2 then p2 else p1

let union_rng (r1 r2 : T.rng) : T.rng =
  if r1.file_name <> r2.file_name
  then r2
  else T.mk_rng r1.file_name (min_pos r1.start_pos r2.start_pos)
                             (max_pos r1.end_pos   r2.end_pos)

let join_range r1 r2 =
  T.range_of_rng (union_rng r1.def_range r2.def_range)
                 (union_rng r1.use_range r2.use_range)

let explode r =
  (r.def_range.file_name,
   r.def_range.start_pos.line,
   r.def_range.start_pos.col,
   r.def_range.end_pos.line,
   r.def_range.end_pos.col)

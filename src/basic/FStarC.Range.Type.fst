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
module FStarC.Range.Type

open FStarC
open FStarC.Effect 

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type file_name = string

(* A source position is a (line, col) pair packed into a single integer,
   with col in the low 16 bits and line above it.

   Ranges hang off every AST node and are serialized into every .checked
   file, so the representation is worth optimizing: as a two-field record a
   [pos] costs a 3-word heap block, whereas packed it is an immediate (zarith
   represents small integers as unboxed OCaml ints).

   The split is chosen so that neither field is a practical limit. A column
   beyond [col_limit] is clamped, so columns get the generous half: 65535 is
   far past the longest line in any real source (the longest in this
   repository is 2713 characters). Lines are not clamped, they merely lose the
   compact encoding: Marshal writes an int in 5 bytes while it fits in 32 bits
   and 9 bytes beyond, so a file over 32767 lines costs 4 extra bytes per
   position but stays exact.

   Packing preserves the lexicographic (line, col) order, so packed positions
   may be compared directly as integers. *)
let col_limit = 65536   (* 2^16 *)

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type pos = int

let pos_line (p:pos) : int = p / col_limit
let pos_col (p:pos) : int = p % col_limit

let max i j = if i < j then j else i

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type rng = {
  file_name:file_name;
  (* ^ Note: this must be a basename, without any directory components. The
  interface should protect this fact. *)
  start_pos:pos;
  end_pos:pos;
}
[@@ PpxDerivingYoJson; PpxDerivingShow ]
type range = {
  def_range:rng;
  use_range:rng
}
let dummy_pos : pos = 0
let dummy_rng = {
  file_name="dummy";
  start_pos=dummy_pos;
  end_pos=dummy_pos
}
let dummyRange = {
  def_range=dummy_rng;
  use_range=dummy_rng
}
let use_range r = r.use_range
let def_range r = r.def_range
let range_of_rng d u = {
    def_range=d;
    use_range=u
}
let set_use_range r2 use_rng =
  if use_rng <> dummy_rng then
    {r2 with use_range=use_rng; def_range=(if r2.def_range=dummy_rng then use_rng else r2.def_range)}
  else r2
let set_def_range r2 def_rng =
  if def_rng <> dummy_rng then
    {r2 with def_range=def_rng}
  else r2
let mk_pos l c : pos =
    let l = max 0 l in
    let c = max 0 c in
    l * col_limit + (if c >= col_limit then col_limit - 1 else c)
let mk_rng file_name start_pos end_pos = {
    file_name = Filepath.basename file_name;
    start_pos = start_pos;
    end_pos   = end_pos
}

let mk_range f b e = let r = mk_rng f b e in range_of_rng r r

open FStarC.Json
let json_of_pos (r: pos): json
  = JsonAssoc [
      "line", JsonInt (pos_line r);
      "col", JsonInt (pos_col r);
    ]
let json_of_rng (r: rng): json
  = JsonAssoc [
      "file_name", JsonStr r.file_name;
      "start_pos", json_of_pos r.start_pos;
      "end_pos", json_of_pos r.end_pos;
    ]
let json_of_range (r: range): json
  = JsonAssoc [
      "def", json_of_rng r.def_range;
      "use", json_of_rng r.use_range;
    ]

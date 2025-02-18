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
open FStarC.Class.Deq
open FStarC.Class.Ord
open FStarC.Order

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type file_name = string

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type pos = {
  line:int;
  col: int
}
let max i j = if i < j then j else i

let compare_pos (p1 p2 : pos) : order =
  lex (cmp p1.line p2.line) (fun _ -> cmp p1.col p2.col)

instance deq_pos : deq pos = { (=?) = (=); }

instance ord_pos : ord pos = {
  super = deq_pos;
  cmp = compare_pos;
}

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
let dummy_pos = {
  line=0;
  col=0;
}
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
    {r2 with use_range=use_rng}
  else r2
let set_def_range r2 def_rng =
  if def_rng <> dummy_rng then
    {r2 with def_range=def_rng}
  else r2
let mk_pos l c = {
    line=max 0 l;
    col=max 0 c
}
let mk_rng file_name start_pos end_pos = {
    file_name = Filepath.basename file_name;
    start_pos = start_pos;
    end_pos   = end_pos
}

let mk_range f b e = let r = mk_rng f b e in range_of_rng r r

open FStarC.Json
let json_of_pos (r: pos): json
  = JsonAssoc [
      "line", JsonInt r.line;
      "col", JsonInt r.col;
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

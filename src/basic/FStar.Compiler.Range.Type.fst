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
module FStar.Compiler.Range.Type

open FStar.Compiler.Effect 

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type file_name = string

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type pos = {
  line:int;
  col: int
}
let max i j = if i < j then j else i
let pos_geq p1 p2 =
   (p1.line > p2.line ||
   (p1.line = p2.line && p1.col >= p2.col))

[@@ PpxDerivingYoJson; PpxDerivingShow ]
type rng = {
  file_name:file_name;
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
  file_name=" dummy";
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
    file_name = file_name;
    start_pos = start_pos;
    end_pos   = end_pos
}

let mk_range f b e = let r = mk_rng f b e in range_of_rng r r

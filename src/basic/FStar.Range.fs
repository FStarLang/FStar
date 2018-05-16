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
#light "off"
// (c) Microsoft Corporation. All rights reserved
module FStar.Range
open FStar.ST
open FStar.All
open FStar.BaseTypes
open FStar.Util

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type file_name = string

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type pos = {
  line:int;
  col: int
}
let max i j = if i < j then j else i
let pos_geq p1 p2 =
   (p1.line > p2.line ||
   (p1.line = p2.line && p1.col >= p2.col))

// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type rng = {
  file_name:file_name;
  start_pos:pos;
  end_pos:pos;
}
// IN F*: [@ PpxDerivingYoJson PpxDerivingShow ]
type range = {
  def_range:rng;
  use_range:rng
}
let dummy_pos = {
  line=0;
  col=0;
}
let dummy_rng = {
  file_name="<dummy>";
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
let union_rng r1 r2 =
  if r1.file_name <> r2.file_name then r2
  else let start_pos =
           if pos_geq r1.start_pos r2.start_pos then
             r2.start_pos
           else r1.start_pos in
       let end_pos =
           if pos_geq r1.end_pos r2.end_pos then
             r1.end_pos
           else r2.end_pos in
       mk_rng r1.file_name start_pos end_pos
let union_ranges r1 r2 = {
  def_range=union_rng r1.def_range r2.def_range;
  use_range=union_rng r1.use_range r2.use_range
}
let rng_included r1 r2 =
    if r1.file_name <> r2.file_name then false
    else pos_geq r1.start_pos r2.start_pos &&
         pos_geq r2.end_pos r1.end_pos
let string_of_pos pos =
    format2 "%s,%s" (string_of_int pos.line) (string_of_int pos.col)
let string_of_file_name f =
    if Options.ide()
    then begin
        match FStar.Options.find_file (FStar.Util.basename f) with
        | None -> f //couldn't find file; just return the relative path
        | Some absolute_path ->
            absolute_path
    end
    else f
let file_of_range r       =
    let f = r.def_range.file_name in
    string_of_file_name f
let set_file_of_range r (f:string) = {r with def_range = {r.def_range with file_name = f}}
let string_of_rng r =
    format3 "%s(%s-%s)" (string_of_file_name r.file_name) (string_of_pos r.start_pos) (string_of_pos r.end_pos)
let string_of_def_range r = string_of_rng r.def_range
let string_of_use_range r = string_of_rng r.use_range
let string_of_range r     = string_of_def_range r

let start_of_range r      = r.def_range.start_pos
let end_of_range r        = r.def_range.end_pos

let file_of_use_range r   = r.use_range.file_name
let start_of_use_range r  = r.use_range.start_pos
let end_of_use_range r    = r.use_range.end_pos

let line_of_pos p         = p.line
let col_of_pos p          = p.col

let end_range r           = mk_range r.def_range.file_name r.def_range.end_pos r.def_range.end_pos

let compare_rng r1 r2     =
    let fcomp = String.compare r1.file_name r2.file_name in
    if fcomp = 0
    then let start1 = r1.start_pos in
         let start2 = r2.start_pos in
         let lcomp = start1.line - start2.line in
         if lcomp = 0
         then start1.col - start2.col
         else lcomp
    else fcomp
let compare r1 r2 = compare_rng r1.def_range r2.def_range
let compare_use_range r1 r2 = compare_rng r1.use_range r2.use_range
let range_before_pos m1 p =
    pos_geq p (end_of_range m1)
let end_of_line p = {p with col=max_int}
let extend_to_end_of_line r = mk_range (file_of_range r)
                                       (start_of_range r)
                                       (end_of_line (end_of_range r))

(* This needs to correspond with the `range` type is ulib/ml/prims.ml,
 * but sadly we cannot use Prims.range here *)
let prims_to_fstar_range (r : (string * (int * int) * (int * int)) * (string * (int * int) * (int * int))) : range =
    let (r1, r2) = r in
    let (f1, s1, e1) = r1 in
    let (f2, s2, e2) = r2 in
    let s1 = mk_pos (fst s1) (snd s1) in
    let e1 = mk_pos (fst e1) (snd e1) in
    let s2 = mk_pos (fst s2) (snd s2) in
    let e2 = mk_pos (fst e2) (snd e2) in
    let r1 = mk_rng f1 s1 e1 in
    let r2 = mk_rng f2 s2 e2 in
    { def_range = r1; use_range = r2 }

let json_of_pos pos =
  JsonList [JsonInt (line_of_pos pos); JsonInt (col_of_pos pos)]

let json_of_range_fields file b e =
  JsonAssoc [("fname", JsonStr file);
             ("beg", json_of_pos b);
             ("end", json_of_pos e)]

let json_of_use_range r =
    json_of_range_fields
            (file_of_use_range r)
            (start_of_use_range r)
            (end_of_use_range r)

let json_of_def_range r =
    json_of_range_fields
            (file_of_range r)
            (start_of_range r)
            (end_of_range r)

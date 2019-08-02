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
module UnionFind
open FStar.Heap


type elem = ref content
and content =
| Link: elem -> content
| Root: nat -> content


val find: x:elem ->
  ST elem
    (requires (fun _ -> True))
    (ensures (fun h_0 y h_1 ->
      Root? (Heap.sel h_1 y) /\
      (forall z. Link? (Heap.sel h_0 z) ==> Link? (Heap.sel h_1 z)) /\
      (forall z. Root? (Heap.sel h_0 z) ==> Root? (Heap.sel h_1 z))))
let rec find x =
  match !x with
  | Link r ->
      let r' = find r in
      x := Link r';
      r'
  | Root _ ->
      x


val link: x:elem -> y:elem ->
  ST elem
    (requires (fun h -> Root? (Heap.sel h x) /\ Root? (Heap.sel h y)))
    (ensures (fun _ _ _ -> True))
let link x y =
  if x = y then
    x
  else match !x, !y with
  | Root rx, Root ry ->
      if rx < ry then begin
        x := Link y; y
      end else if rx > ry then begin
        y := Link x; x
      end else begin
        y := Link x;
        x := Root (rx + 1);
        x
      end


val union: elem -> elem -> St elem
let union x y =
  let rx = find x in
  let ry = find y in
  let t = !ry in
  link rx ry


val equiv: elem -> elem -> St bool
let equiv x y =
  find x = find y

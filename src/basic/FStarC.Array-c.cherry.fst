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
module FStarC.Array

(* The Cherry implementation: a reference to an immutable array.  [set] takes
   the array out of the reference before updating it, so that it is uniquely
   owned and Cherry's [upd] changes it in place. *)

open FStarC.Effect
module S = FStarC.SmallInt
module IA = FStar.ImmutableArray

type array (a:Type) = ref (IA.t a)

let rec push_n (#a:Type) (arr:IA.t a) (n:nat) (x:a) : Tot (IA.t a) (decreases n) =
  if n = 0 then arr else push_n (IA.push arr x) (n - 1) x

let make #a n x =
  let n = S.to_int n in
  if n < 0 then failwith "FStarC.Array.make: negative length"
  else mk_ref (push_n (IA.of_list []) n x)

let length #a arr = S.of_int (IA.length !arr)

let pos (len:nat) (i:S.t) : ML (j:nat{j < len}) =
  let j = S.to_int i in
  if 0 <= j && j < len then j
  else failwith "FStarC.Array: index out of bounds"

let get #a arr i =
  let cur = !arr in
  IA.index cur (pos (IA.length cur) i)

let set #a arr i x =
  let cur = !arr in
  let j = pos (IA.length cur) i in
  arr := IA.of_list [];
  arr := IA.upd cur j x

let rec push_from (#a:Type) (acc:IA.t a) (src:IA.t a) (i:nat) : Tot (IA.t a) (decreases (IA.length src - i)) =
  if i >= IA.length src then acc
  else push_from (IA.push acc (IA.index src i)) src (i + 1)

let append #a arr1 arr2 =
  (* The first push copies [!arr1], which [arr1] still refers to. *)
  mk_ref (push_from !arr1 !arr2 0)

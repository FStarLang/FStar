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
module FStarC.Vec

(* The OCaml implementation: an array twice as large as needed, and how much
   of it is in use. *)

open FStarC.Effect
module I = FStarC.SmallInt
module A = FStarC.Array

noeq type vec_ (a:Type) = {
  len  : ref I.t;
  data : ref (A.array a);
}

type vec (a:Type) = vec_ a

let singleton #a x = { len = mk_ref I.one; data = mk_ref (A.make (I.of_int 16) x) }

let length #a v = !v.len

let get #a v i =
  if I.(i >= zero && i < !v.len) then A.get !v.data i
  else failwith "FStarC.Vec: index out of bounds"

let push #a v x =
  let n = !v.len in
  let d = !v.data in
  (if I.(n >= A.length d) then begin
     let d = A.append d d in
     A.set d n x;
     v.data := d
   end else A.set d n x);
  v.len := I.(n + one)

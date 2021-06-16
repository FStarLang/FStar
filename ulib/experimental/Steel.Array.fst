(*
   Copyright 2020 Microsoft Research

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

module Steel.Array

open Steel.Effect.Atomic
open Steel.Reference

let array t = ref (Seq.seq t)

let is_array r = ptr r
let array_sel r = ptr_sel r

let malloc x n =
  let s = Seq.create (U32.v n) x in
  malloc s

let index r i =
  let h = get() in
  let s = read r in
  Seq.index s (U32.v i)

let upd r i x =
  let s = read r in
  let s' = Seq.upd s (U32.v i) x in
  write r s'

let free r = free r

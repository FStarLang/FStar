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
open FStar.Ghost
let array t = l:erased nat & ref (Seq.lseq t l)

let length #t (x:array t) = dfst x
let is_array r = ptr (dsnd r)
let array_sel r = ptr_sel (dsnd r)

let malloc #a x n =
  let l : erased nat = hide (U32.v n) in
  let s : Seq.lseq a l = Seq.create (U32.v n) x in
  let p : ref (Seq.lseq a l) = malloc s in
  let x : array a = (| l, p |) in
  Steel.Effect.Atomic.return x

let index r i =
  let h = get() in
  let s = read (dsnd r) in
  Seq.index s (U32.v i)

let upd r i x =
  let s = read (dsnd r) in
  let s' = Seq.upd s (U32.v i) x in
  write (dsnd r) s'

let free r = free (dsnd r)

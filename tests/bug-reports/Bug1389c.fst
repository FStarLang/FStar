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
module Bug1389C

open FStar.Ghost
open FStar.Seq
open FStar.Ref

type t = (s:seq (ref int){length s > 0})

let contains (s:t) (x:ref int) : GTot Type0 =
  (exists (i:nat{i < length s}). index s i == x)

let foo (s:t) (x:ref int{s `contains` x}) :
  GTot (unit * seq (ref int))
    (decreases (length s)) // This decreases turns the GTot into GHOST internally, exposing the bug
  = (), s

val fail: es:erased t -> x:ref int{Ghost.reveal es `contains` x} ->
  Tot (erased t)
let fail es x =
  let es = elift2_p foo es (Ghost.hide x) in
  assert (False); // this DEFINITELY should NOT go through
  es // this should NOT type check

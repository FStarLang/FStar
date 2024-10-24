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
module Bug1206

open FStar.Tactics.V2
open FStar.HyperStack.ST

#reset-options "--max_fuel 1 --max_ifuel 1"

type bslice =
| BSlice : len:nat -> bslice

let serializer_ty  = buf:bslice -> Stack (option (off:nat{off <= buf.len}))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))

let ser_id (s1: serializer_ty) : serializer_ty =
  fun buf -> match s1 buf with
  | Some off -> Some off
  | None -> None

assume val ser : serializer_ty

let normalize (#t:Type) (x:t) : Tac unit =
  dup ();
  exact (quote x);
  norm [delta];
  trefl ()

let ser' : serializer_ty = _ by (normalize (ser_id ser))


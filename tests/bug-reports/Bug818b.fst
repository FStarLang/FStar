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
module Bug818b

open FStar.ST
open FStar.Heap

assume type matrix
type sshuffle = heap -> Tot heap
val siter: n:nat -> (f: 'a -> Tot 'a) -> 'a -> 'a
let rec siter n f x = if n = 0 then x else siter (n-1) f (f x)

type shuffle (spec: sshuffle) =
  m:matrix -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> spec h0 == spec h0))

val iter: n:nat -> spec: sshuffle -> body: shuffle spec -> shuffle (siter (n+1) spec)
let rec iter n spec body m =
  if n <> 0 then (
    body m;
    admit();
    iter (n - 1) spec body m )

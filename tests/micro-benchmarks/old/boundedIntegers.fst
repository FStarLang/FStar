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
module FStar.BoundedIntegers

val int32_min_value : int
let int32_min_value = -2147483647

val int32_max_value : int
let int32_max_value = 2147483647

assume val uint32_max_value : int
(*let uint32_max_value = 4294967295*)

opaque type Within_Int32 (i:int) =
    int32_min_value <= i /\ i <= int32_max_value

private opaque type Int32 (i:int) =
  Within_Int32 i

opaque type Within_UInt32 (i:int) =
    0 <= i /\ i <= uint32_max_value

private opaque type UInt32 (i:int) =
   Within_UInt32 i

type int32 = i:int{Int32 i}
type uint32 = i:int{UInt32 i}

val int32_unfold: i:int
               -> Lemma
               (requires (Int32 i))
               (ensures (Within_Int32 i))
               [SMTPat (Int32 i)]
let int32_unfold i = ()

val uint32_unfold: i:int
               -> Lemma
               (requires (UInt32 i))
               (ensures (Within_UInt32 i))
               [SMTPat (UInt32 i)]
let uint32_unfold i = ()

val int32_add:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i + j)
            ==> Int32 (i + j)))
  [SMTPat (Int32 (i + j))]
let int32_add i j = ()

val int32_sub:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i - j)
            ==> Int32 (i - j)))
  [SMTPat (Int32 (i - j))]
let int32_sub i j = ()

val int32_mul:i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i * j)
            ==> Int32 (i * j)))
  [SMTPat (Int32 (i * j))]
let int32_mul i j = ()

val int32_div:i:nat
          -> j:nonzero
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (i / j)
            ==> Int32 (i / j)))
  [SMTPat (Int32 (i / j))]
let int32_div i j = ()

(*val int32_op: op:(int -> int -> Tot int)
          -> i:int
          -> j:int
          -> Lemma
  (requires True)
  (ensures (Int32 i /\ Int32 j /\ Within_Int32 (op i j)
            ==> Int32 (op i j)))
  [SMTPat (Int32 (op i j))]
let int32_op op i j = ()

val uint32_op: op:(int -> int -> Tot int)
            -> i:int
            -> j:int
            -> Lemma
  (requires True)
  (ensures (UInt32 i /\ UInt32 j /\ Within_UInt32 (op i j)
            ==> UInt32 (op i j)))
  [SMTPat (UInt32 (op i j))]
let uint32_op op i j = ()*)


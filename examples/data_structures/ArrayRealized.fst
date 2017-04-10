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

(* A logical theory of integer-indexed arrays, from [0, n) *)
module ArrayRealized

noeq type contents (a:Type u#a) : Type u#a =
  | Const : v:a -> contents a
  | Upd   : ix:int -> v:a -> tl:contents a -> contents a
  | Append : s1:seq a -> s2:seq a -> contents a

and seq (a:Type u#a) : Type u#a =
  | Seq : c:contents a
          -> start_i:nat
          -> end_i:nat{end_i >= start_i}
          -> seq a

val create: n:nat -> init:'a -> Tot (seq 'a)
let create n init = Seq (Const init) 0 n

val length: s:seq 'a -> Tot nat
let length s = Seq?.end_i s - Seq?.start_i s

val __index__: contents 'a -> int -> Tot 'a
let rec __index__ c i = match c with
  | Const v -> v
  | Upd j v tl -> if i=j then v else __index__ tl i
  | Append s1 s2 -> if i < length s1 then __index__ (Seq?.c s1) i else __index__ (Seq?.c s2) (i - length s1)

val index: s:seq 'a -> i:nat{length s > i} -> Tot 'a
let index (Seq c j k) i = __index__ c (i + j)

val __update__: contents 'a -> int -> 'a -> Tot (contents 'a)
let rec __update__ c i v = match c with
  | Const _
  | Upd _ _ _ -> Upd i v c
  | Append s1 s2 ->
     if i < length s1
     then Append (Seq (__update__ (Seq?.c s1) i v) (Seq?.start_i s1) (Seq?.end_i s1)) s2
     else Append s1 (Seq (__update__ (Seq?.c s2) (i - length s1) v) (Seq?.start_i s2) (Seq?.end_i s2))

val update: s:seq 'a -> i:nat{length s > i} -> v:'a -> Tot (seq 'a)
let update (Seq c j k) i v = Seq (__update__ c (i + j) v) j k

val slice: s:seq 'a -> i:nat -> j:nat{(i <= j /\ j <= length s)} -> Tot (seq 'a)
let slice (Seq c start_i end_i) i j = Seq c (start_i + i) (start_i + j)

val split: s:seq 'a -> i:nat{(0 <= i /\ i < length s)} -> Tot (seq 'a * seq 'a)
let split s i = slice s 0 i, slice s i (length s)

val append: seq 'a -> seq 'a -> Tot (seq 'a)
let append s1 s2 = Seq (Append s1 s2) 0 (length s1 + length s2)

type equal (#a:Type) (s1:seq a) (s2:seq a) =
          (length s1 == length s2
           /\ (forall (i:int).
                 (0 <= i /\ i < length s1)
               ==> __index__ (Seq?.c s1) i == __index__ (Seq?.c s2) i))

assume val eq: #a:Type -> s1:seq a -> s2:seq a -> Tot (b:bool{b ==> equal s1 s2})

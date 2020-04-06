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
module FStar.DM4F.OTP.Heap

open FStar.BitVector
open FStar.Seq

(***** Random tape *****)

let size = 10

val q: pos

let elem = bv_t q

val id : eqtype

val tape : eqtype

val to_id (n:nat{n < size}) : id

val incrementable: id -> bool

val incr (i:id{incrementable i}) : id

val index (h:tape) (i:id) : Tot elem
let sel = index

val upd (h:tape) (i:id) (x:elem) : Tot tape

val create (x:elem) : Tot tape

val equal: tape -> tape -> GTot Type0

val lemma_eq_intro: s1:tape -> s2:tape -> Lemma
  (requires ((forall (i:id).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i)))
  (ensures (equal s1 s2))
  [SMTPat (equal s1 s2)]

val lemma_eq_elim: s1:tape -> s2:tape -> Lemma
  (requires (equal s1 s2))
  (ensures (s1==s2))
  [SMTPat (equal s1 s2)]

val lemma_index_upd1: s:tape -> n:id -> v:elem -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v))
  [SMTPat (index (upd s n v) n)]

val lemma_index_upd2: s:tape -> n:id -> v:elem -> i:id{i<>n} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i))
  [SMTPat (index (upd s n v) i)]

val lemma_index_create: v:elem -> i:id -> Lemma
  (requires True)
  (ensures (index (create v) i == v))
  [SMTPat (index (create v) i)]

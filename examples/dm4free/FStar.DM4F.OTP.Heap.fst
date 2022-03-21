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

let q = admit ()

type id : eqtype = i:nat{i < size}

type tape : eqtype = h:seq elem{length h == size}

let to_id (n:nat{n < size}) : id = n

let incrementable (i:id) = i + 1 < size

let incr (i:id{incrementable i}) : id = to_id (i + 1)

let index (h:tape) (i:id) : Tot elem = index h i

let upd (h:tape) (i:id) (x:elem) : Tot tape = upd h i x

let create (x:elem) : Tot tape = create #elem size x

let equal (t1:tape) (t2:tape) = Seq.equal t1 t2

let lemma_eq_intro s1 s2 =
  assert (forall (i:id). index s1 i == Seq.index s1 i);
  assert (forall (i:id). index s2 i == Seq.index s2 i);
  Seq.lemma_eq_intro #elem s1 s2

let lemma_eq_elim s1 s2 = ()

let lemma_index_upd1 s n v = lemma_index_upd1 #elem s n v

let lemma_index_upd2 s n v i = lemma_index_upd2 #elem s n v i

let lemma_index_create v i = lemma_index_create #elem size v i

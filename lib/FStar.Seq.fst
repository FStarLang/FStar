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
(* A logical theory of sequences indexed by natural numbers in [0, n) *)
module FStar.Seq
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"


(* Representation hidden from clients *)
// type seq : Type -> Type
abstract type seq (a:Type) =
| MkSeq: length:nat -> contents:(n:nat{n<length} -> Tot a) -> seq a

(* Operator for concatenation *)
assume val op_At_Bar: #a:Type -> seq a -> seq a -> Tot (seq a)

(* Primitive operations on sequences *)
abstract val length: #a:Type -> seq a -> Tot nat
let length s = MkSeq.length s
(*
(match s with
  | MkSeq l c -> l)
*)

abstract val mkSeqContents : s:(seq 'a) -> n:nat{n<length s} -> Tot 'a
let mkSeqContents s n = MkSeq.contents s n
(*
(match s with
| MkSeq l c -> c n)
*)

abstract val create: #a:Type -> nat -> a -> Tot (seq a)
let create len v =  MkSeq len (fun i -> v)

abstract val exFalso0 : a:Type -> n:nat{n<0} -> Tot a
let exFalso0 'a n = ()

abstract val createEmpty: #a:Type -> Tot (s:(seq a){length s=0})
let createEmpty 'a =  (MkSeq 0 (fun i -> (exFalso0 'a i)))

abstract val index: #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a
let index s i = mkSeqContents s i

abstract val upd: #a:Type -> s:seq a -> n:nat{n < length s} -> a ->  Tot (seq a)
let upd s n v =
 MkSeq (length s) (fun i -> if i=n then v else (mkSeqContents s) i)

abstract val append: #a:Type -> seq a -> seq a -> Tot (seq a)
let append s1 s2 =
  MkSeq (length s1 + length s2) (fun x -> if x < (length s1) then index s1 x else index s2 (x - (length s1)))

abstract val slice:  #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (seq a)
let slice s i j =
  MkSeq (j-i) (fun x -> index s (x + i))

(* Lemmas about length *)
abstract val lemma_create_len: #a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]

abstract val lemma_len_upd: #a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd s n v) = length s))
  [SMTPat (length (upd s n v))]

abstract val lemma_len_append: #a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]

abstract val lemma_len_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i))
  [SMTPat (length (slice s i j))]

let lemma_create_len n i   = ()
let lemma_len_upd n v s    = ()
let lemma_len_append s1 s2 = ()
let lemma_len_slice s i j  = ()

(* Lemmas about index *)
abstract val lemma_index_create: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i = v))
  [SMTPat (index (create n v) i)]

abstract val lemma_index_upd1: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd s n v) n = v))
  [SMTPat (index (upd s n v) n)]

abstract val lemma_index_upd2: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i = index s i))
  [SMTPat (index (upd s n v) i)]

abstract val lemma_index_app1: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s1 i))
  [SMTPat (index (append s1 s2) i)]

abstract val lemma_index_app2: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i = index s2 (i - length s1)))
  [SMTPat (index (append s1 s2) i)]

abstract val lemma_index_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k = index s (k + i)))
  [SMTPat (index (slice s i j) k)]

let lemma_index_create n v i  = ()
let lemma_index_upd1 n v s    = ()
let lemma_index_upd2 n v s i  = ()
let lemma_index_app1 s1 s2 i  = ()
let lemma_index_app2 s2 s2 i  = ()
let lemma_index_slice s i j k = ()

//type Eq: #a:Type -> seq a -> seq a -> Type
opaque type Eq (#a:Type) (s1:seq a) (s2:seq a) =
  (length s1 = length s2
   /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))

(*This should be provable now*)
assume Extensionality: forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Eq s1 s2)} Eq s1 s2 <==> (s1=s2)

(* Extensionality *)
abstract val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (length s1 = length s2
               /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i))))
     (ensures (Eq s1 s2))
     [SMTPatT (Eq s1 s2)]

abstract val lemma_eq_refl: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (s1 = s2))
     (ensures (Eq s1 s2))
     [SMTPatT (Eq s1 s2)]

abstract val lemma_eq_elim: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (Eq s1 s2))
     (ensures (s1=s2))
     [SMTPatT (Eq s1 s2)]

let lemma_eq_intro s1 s2 = ()
let lemma_eq_refl s1 s2  = ()
let lemma_eq_elim s1 s2  = ()

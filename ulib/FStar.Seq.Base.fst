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
module FStar.Seq.Base
//#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

module List = FStar.List.Tot

abstract type seq (a:Type u#a) :Type u#a =
  | MkSeq: l:list a -> seq a

(* Destructors *)
abstract val length: #a:Type -> seq a -> Tot nat
let length #a s = List.length (MkSeq?.l s)

abstract val index:  #a:Type -> s:seq a -> i:nat{i < length s} -> Tot a
let index #a s i = List.index (MkSeq?.l s) i

private abstract val cons: #a:Type -> x:a -> s:seq a -> Tot (seq a)
let cons #a x s = MkSeq (x::(MkSeq?.l s))

private abstract val hd: #a:Type -> s:seq a{length s > 0} -> Tot a
let hd #a s = List.hd (MkSeq?.l s)

private abstract val tl: #a:Type -> s:seq a{length s > 0} -> Tot (seq a)
let tl #a s = MkSeq (List.tl (MkSeq?.l s))

abstract val create: #a:Type -> nat -> a -> Tot (seq a)
let rec create #a len v = if len = 0 then MkSeq [] else cons v (create (len - 1) v)

private abstract let rec init_aux (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> Tot a))
  :Tot (seq a) (decreases (len - k))
  = if k + 1 = len
    then MkSeq [contents k]
    else cons (contents k) (init_aux len (k+1) contents)

inline_for_extraction abstract val init: #a:Type -> len:nat -> contents: (i:nat { i < len } -> Tot a) -> Tot (seq a)
inline_for_extraction abstract let init #a len contents = if len = 0 then MkSeq [] else init_aux len 0 contents

abstract val of_list: #a:Type -> list a -> Tot (seq a)
let of_list #a l = MkSeq l

let lemma_of_list_length (#a:Type) (l:list a)
  : Lemma (ensures (length (of_list #a l) == List.length l))
          [SMTPat (length (of_list #a l))]
  = ()

let lemma_of_list (#a:Type) (l:list a) (i:nat{i < List.length l})
  : Lemma (ensures (index (of_list #a l) i == List.index l i))
          [SMTPat (index (of_list #a l) i)]
  = ()

abstract
let empty #a : Tot (s:(seq a){length s=0}) = MkSeq []

[@(deprecated "Seq.empty")]
unfold
let createEmpty (#a:Type)
    : Tot (s:(seq a){length s=0})
    = empty #a

let lemma_empty (#a:Type) (s:seq a) : Lemma (length s = 0 ==> s == empty #a) = ()

abstract val upd: #a:Type -> s:seq a -> n:nat{n < length s} -> a ->  Tot (seq a) (decreases (length s))
let rec upd #a s n v = if n = 0 then cons v (tl s) else cons (hd s) (upd (tl s) (n - 1) v)

abstract val append: #a:Type -> seq a -> seq a -> Tot (seq a)
let append #a s1 s2 = MkSeq (List.append (MkSeq?.l s1) (MkSeq?.l s2))

let op_At_Bar (#a:Type) (s1:seq a) (s2:seq a) = append s1 s2

abstract val slice:  #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Tot (r:seq a) (decreases (length s))
let rec slice #a s i j =
  if i > 0 then slice #a (tl s) (i - 1) (j - 1)
  else
    if j = 0 then MkSeq []
    else cons (hd s) (slice #a (tl s) i (j - 1))

(* Lemmas about length *)
abstract val lemma_create_len: #a:Type -> n:nat -> i:a -> Lemma
  (requires True)
  (ensures (length (create n i) = n))
  [SMTPat (length (create n i))]
let rec lemma_create_len #a n i = if n = 0 then () else lemma_create_len #a (n - 1) i

abstract val lemma_init_len: #a:Type -> n:nat -> contents: (i:nat { i < n } -> Tot a) -> Lemma
  (requires True)
  (ensures (length (init n contents) = n))
  [SMTPat (length (init n contents))]
private
let rec lemma_init_aux_len (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> Tot a))
  : Lemma (requires True)
    (ensures (length (init_aux n k contents) = n - k))
    (decreases (n-k))
    [SMTPat (length (init_aux n k contents))]
=
  if k + 1 = n then () else lemma_init_aux_len #a n (k+1) contents

let rec lemma_init_len #a n contents = if n = 0 then () else lemma_init_aux_len #a n 0 contents

abstract val lemma_len_upd: #a:Type -> n:nat -> v:a -> s:seq a{n < length s} -> Lemma
  (requires True)
  (ensures (length (upd s n v) = length s))
  [SMTPat (length (upd s n v))]
let rec lemma_len_upd #a n v s = if n = 0 then () else lemma_len_upd #a (n - 1) v (tl s)

abstract val lemma_len_append: #a:Type -> s1:seq a -> s2:seq a -> Lemma
  (requires True)
  (ensures (length (append s1 s2) = length s1 + length s2))
  [SMTPat (length (append s1 s2))]
let lemma_len_append #a s1 s2 = FStar.List.Tot.append_length (MkSeq?.l s1) (MkSeq?.l s2)

abstract val lemma_len_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j && j <= length s} -> Lemma
  (requires True)
  (ensures (length (slice s i j) = j - i)) (decreases (length s))
  [SMTPat (length (slice s i j))]
let rec lemma_len_slice #a s i j  =
  if i > 0 then lemma_len_slice #a (tl s) (i - 1) (j - 1)
  else if j = 0 then ()
  else lemma_len_slice #a (tl s) i (j - 1)

(* Lemmas about index *)
abstract val lemma_index_create: #a:Type -> n:nat -> v:a -> i:nat{i < n} -> Lemma
  (requires True)
  (ensures (index (create n v) i == v))
  [SMTPat (index (create n v) i)]
let rec lemma_index_create #a n v i =
  if n = 0 then ()
  else
    if i = 0 then () else lemma_index_create #a (n - 1) v (i - 1)

abstract val lemma_index_upd1: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> Lemma
  (requires True)
  (ensures (index (upd s n v) n == v)) (decreases (length s))
  [SMTPat (index (upd s n v) n)]
let rec lemma_index_upd1 #a s n v = if n = 0 then () else lemma_index_upd1 #a (tl s) (n - 1) v

abstract val lemma_index_upd2: #a:Type -> s:seq a -> n:nat{n < length s} -> v:a -> i:nat{i<>n /\ i < length s} -> Lemma
  (requires True)
  (ensures (index (upd s n v) i == index s i)) (decreases (length s))
  [SMTPat (index (upd s n v) i)]
let rec lemma_index_upd2 #a s n v i = match (MkSeq?.l s) with
  | []     -> ()
  | hd::tl  ->
    if i = 0 then ()
    else
      if n = 0 then ()
      else lemma_index_upd2 #a (MkSeq tl) (n - 1) v (i - 1)

abstract val lemma_index_app1: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s1 i)) (decreases (length s1))
  [SMTPat (index (append s1 s2) i)]
let rec lemma_index_app1 #a s1 s2 i  = match (MkSeq?.l s1) with
  | []    -> ()
  | hd::tl ->
    if i = 0 then () else lemma_index_app1 #a (MkSeq tl) s2 (i - 1)

abstract val lemma_index_app2: #a:Type -> s1:seq a -> s2:seq a -> i:nat{i < length s1 + length s2 /\ length s1 <= i} -> Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s2 (i - length s1))) (decreases (length s1))
  [SMTPat (index (append s1 s2) i)]
let rec lemma_index_app2 #a s1 s2 i  = match s1.l with
  | []    -> ()
  | hd::tl -> lemma_index_app2 #a (MkSeq tl) s2 (i - 1)

abstract val lemma_index_slice: #a:Type -> s:seq a -> i:nat -> j:nat{i <= j /\ j <= length s} -> k:nat{k < j - i} -> Lemma
  (requires True)
  (ensures (index (slice s i j) k == index s (k + i))) (decreases (length s))
  [SMTPat (index (slice s i j) k)]
let rec lemma_index_slice #a s i j k =
  if i > 0 then lemma_index_slice #a (tl s) (i - 1) (j - 1) k
  else
    if j = 0 then ()
    else if k = 0 then () else lemma_index_slice #a (tl s) i (j - 1) (k - 1)

val hasEq_lemma: a:Type -> Lemma (requires (hasEq a)) (ensures (hasEq (seq a))) [SMTPat (hasEq  (seq a))]
let hasEq_lemma a = ()

abstract type equal (#a:Type) (s1:seq a) (s2:seq a) =
  (length s1 = length s2
   /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))

(* decidable equality *)
private val eq_i:
  #a:eqtype -> s1:seq a -> s2:seq a{length s1 = length s2}
  -> i:nat{i <= length s1}
  -> Tot (r:bool{r <==> (forall j. (j >= i /\ j < length s1) ==> (index s1 j = index s2 j))})
    (decreases (length s1 - i))
let rec eq_i #a s1 s2 i =
  if i = length s1 then true
  else
    if index s1 i = index s2 i then eq_i s1 s2 (i + 1)
    else false

abstract val eq: #a:eqtype -> s1:seq a -> s2:seq a -> Tot (r:bool{r <==> equal s1 s2})
let eq #a s1 s2 = if length s1 = length s2 then eq_i s1 s2 0 else false

abstract val lemma_eq_intro: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (length s1 = length s2
               /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i))))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]
let lemma_eq_intro #a s1 s2 = ()

abstract val lemma_eq_refl: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (s1 == s2))
     (ensures (equal s1 s2))
     [SMTPat (equal s1 s2)]
let lemma_eq_refl #a s1 s2  = ()

abstract val lemma_eq_elim: #a:Type -> s1:seq a -> s2:seq a -> Lemma
     (requires (equal s1 s2))
     (ensures (s1==s2))
     [SMTPat (equal s1 s2)]
let lemma_eq_elim #a s1 s2  =
  assert ( length s1 == List.length (MkSeq?.l s1) );
  assert ( length s2 == List.length (MkSeq?.l s2) );
  assert ( forall (i: nat) . i < length s1 ==> index s1 i == List.index (MkSeq?.l s1) i);
  assert ( forall (i: nat) . i < length s1 ==> index s2 i == List.index (MkSeq?.l s2) i);
  List.index_extensionality (MkSeq?.l s1) (MkSeq?.l s2)

(* Properties of [append] *)

abstract let append_assoc
  (#a: Type)
  (s1 s2 s3: seq a)
: Lemma
  (ensures (append (append s1 s2) s3 == append s1 (append s2 s3)))
= List.append_assoc (MkSeq?.l s1) (MkSeq?.l s2) (MkSeq?.l s3)

abstract let append_empty_l
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append createEmpty s == s))
= List.append_nil_l (MkSeq?.l s)

abstract let append_empty_r
  (#a: Type)
  (s: seq a)
: Lemma
  (ensures (append s createEmpty == s))
= List.append_l_nil (MkSeq?.l s)


abstract
val init_index (#a:Type) (len:nat) (contents:(i:nat { i < len } -> Tot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len}). index (init len contents) i == contents i))
    [SMTPat (index (init len contents))]

private
let rec init_index_aux (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> Tot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len - k}).index (init_aux len k contents) i == contents (k + i)))
    (decreases (len - k))
=
  if k + 1 = len
  then ()
  else begin
    init_index_aux #a len (k+1) contents ;
    assert (forall (i:nat{i < len - k}).
      if i = 0 then index (init_aux len k contents) 0 == contents k
      else index (init_aux len k contents) i == index (init_aux len (k+1) contents) (i-1))
  end

let init_index #a len contents =
  if len = 0 then () else init_index_aux #a len 0 contents

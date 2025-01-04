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

type seq (a:Type u#a) :Type u#a =
  | MkSeq: l:list a -> seq a

let length #_ s = List.length (MkSeq?.l s)

let seq_to_list #_ s =
  match s with
  | MkSeq l -> l

let seq_of_list #_ l = MkSeq l

let index #_ s i = List.index (MkSeq?.l s) i

let _cons (#a:Type) (x:a) (s:seq a) : Tot (seq a) = MkSeq (x::(MkSeq?.l s))

let hd (#a:Type) (s:seq a{length s > 0}) : Tot a = List.hd (MkSeq?.l s)

let tl (#a:Type) (s:seq a{length s > 0}) : Tot (seq a) = MkSeq (List.tl (MkSeq?.l s))

let rec create #_ len v = if len = 0 then MkSeq [] else _cons v (create (len - 1) v)

private let rec init_aux' (#a:Type) (len:nat) (k:nat{k < len}) (contents: (i:nat{i < len} -> Tot a))
    : Tot (seq a)
      (decreases (len - k))
  = if k + 1 = len
    then MkSeq [contents k]
    else _cons (contents k) (init_aux' len (k+1) contents)

let init_aux = init_aux'

let init #_ len contents = if len = 0 then MkSeq [] else init_aux len 0 contents

private let rec init_aux_ghost' (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> GTot a))
    : GTot (seq a)
      (decreases (len - k))
  = if k + 1 = len
    then MkSeq [contents k]
    else _cons (contents k) (init_aux_ghost' len (k+1) contents)

let init_aux_ghost = init_aux_ghost'

let init_ghost #_ len contents = if len = 0 then MkSeq [] else init_aux_ghost len 0 contents

let empty #_ = MkSeq []

let lemma_empty #_ _ = ()

private let rec upd' (#a:Type) (s:seq a) (n:nat{n < length s}) (v:a)
    : Tot (seq a)
      (decreases (length s))
  = if n = 0 then _cons v (tl s) else _cons (hd s) (upd' (tl s) (n - 1) v)

let upd = upd'

let append #_ s1 s2 = MkSeq (List.append (MkSeq?.l s1) (MkSeq?.l s2))

private let rec slice' (#a:Type) (s:seq a) (i:nat) (j:nat{i <= j && j <= length s})
    : Tot (seq a)
      (decreases (length s))
  =  if i > 0 then slice' #a (tl s) (i - 1) (j - 1)
     else if j = 0 then MkSeq []
          else _cons (hd s) (slice' #a (tl s) i (j - 1))

let slice = slice'

let lemma_seq_of_seq_to_list #_ s = ()
let lemma_seq_to_seq_of_list #_ s = ()
let lemma_seq_of_list_cons #_ x l = ()
let lemma_seq_to_list_cons #_ x s = ()

let rec lemma_create_len #_ n i = if n = 0 then () else lemma_create_len (n - 1) i

let rec lemma_init_aux_len' (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> Tot a))
  : Lemma (requires True)
    (ensures (length (init_aux n k contents) = n - k))
    (decreases (n-k))
= if k + 1 = n then () else lemma_init_aux_len' #a n (k+1) contents

let lemma_init_len #_ n contents = if n = 0 then () else lemma_init_aux_len' n 0 contents

let lemma_init_aux_len = lemma_init_aux_len'

private let rec lemma_init_ghost_aux_len' (#a:Type) (n:nat) (k:nat{k < n}) (contents:(i:nat{ i < n } -> GTot a))
  : Lemma (requires True)
    (ensures (length (init_aux_ghost n k contents) = n - k))
    (decreases (n-k))
= if k + 1 = n then () else lemma_init_ghost_aux_len' #a n (k+1) contents

let lemma_init_ghost_len #_ n contents = if n = 0 then () else lemma_init_ghost_aux_len' n 0 contents

let lemma_init_ghost_aux_len = lemma_init_ghost_aux_len'

let rec lemma_len_upd #_ n v s = if n = 0 then () else lemma_len_upd (n - 1) v (tl s)

let lemma_len_append #_ s1 s2 = FStar.List.Tot.append_length (MkSeq?.l s1) (MkSeq?.l s2)

let rec lemma_len_slice' (#a:Type) (s:seq a) (i:nat) (j:nat{i <= j && j <= length s})
  : Lemma
    (requires True)
    (ensures (length (slice s i j) = j - i)) (decreases (length s))
= if i > 0 then lemma_len_slice' #a (tl s) (i - 1) (j - 1)
  else if j = 0 then ()
  else lemma_len_slice' #a (tl s) i (j - 1)

let lemma_len_slice = lemma_len_slice'

let rec lemma_index_create #_ n v i =
  if n = 0 then ()
  else if i = 0 then ()
       else (lemma_create_len (n - 1) v; lemma_index_create (n - 1) v (i - 1))

let rec lemma_index_upd1' (#a:Type) (s:seq a) (n:nat{n < length s}) (v:a)
  : Lemma
    (requires True)
    (ensures (index (upd s n v) n == v)) (decreases (length s))
= if n = 0
  then ()
  else begin
    lemma_index_upd1' #a (tl s) (n - 1) v;
    assert (index (upd (tl s) (n-1) v) (n-1) == v)
  end

let lemma_index_upd1 = lemma_index_upd1'

let rec lemma_index_upd2' (#a:Type) (s:seq a) (n:nat{n < length s}) (v:a) (i:nat{i<>n /\ i < length s})
  : Lemma
    (requires True)
    (ensures (index (upd s n v) i == index s i))
    (decreases (length s))
= match (MkSeq?.l s) with
  | []     -> ()
  | hd::tl  ->
    if i = 0 then ()
    else
      if n = 0 then ()
      else (lemma_len_upd (n - 1) v (MkSeq tl); lemma_index_upd2' #a (MkSeq tl) (n - 1) v (i - 1))

let lemma_index_upd2 = lemma_index_upd2'

let rec lemma_index_app1' (#a:Type) (s1:seq a) (s2:seq a) (i:nat{i < length s1})
  : Lemma
    (requires True)
    (ensures (index (append s1 s2) i == index s1 i)) (decreases (length s1))
= match (MkSeq?.l s1) with
  | []    -> ()
  | hd::tl ->
    if i = 0 then ()
    else (lemma_len_append (MkSeq tl) s2; lemma_index_app1' #a (MkSeq tl) s2 (i - 1))

let lemma_index_app1 = lemma_index_app1'

let rec lemma_index_app2' (#a:Type) (s1:seq a) (s2:seq a) (i:nat{i < length s1 + length s2 /\ length s1 <= i})
: Lemma
  (requires True)
  (ensures (index (append s1 s2) i == index s2 (i - length s1))) (decreases (length s1))
= match s1.l with
  | []    -> ()
  | hd::tl -> lemma_index_app2' #a (MkSeq tl) s2 (i - 1)

let lemma_index_app2 = lemma_index_app2'

let rec lemma_index_slice0' (#a:Type) (s:seq a) (j:nat{j <= length s}) (k : nat{k < j})
: Lemma
  (requires True)
  (ensures (index (slice s 0 j) k == index s k)) (decreases (length s))
= if k = 0
  then ()
  else lemma_index_slice0' (tl s) (j-1) (k-1)

#push-options "--fuel 1 --ifuel 0"
let rec lemma_index_slice' (#a:Type) (s:seq a) (i:nat) (j:nat{i <= j /\ j <= length s}) (k:nat{k < j - i})
: Lemma
  (requires True)
  (ensures (index (slice s i j) k == index s (k + i))) (decreases (length s))
= if i > 0
  then (
    lemma_index_slice' #a (tl s) (i - 1) (j - 1) k;
    assert (index (slice (tl s) (i - 1) (j - 1)) k == index (tl s) (k + (i - 1)));
    assert (index (slice (tl s) (i - 1) (j - 1)) k == index s (k + i));
    assert (index (slice s i j) k == index s (k + i))
  )
  else (
    assert (j > 0);
    lemma_index_slice0' #a s j k
  )
#pop-options

let lemma_index_slice = lemma_index_slice'

let hasEq_lemma _ = ()

let equal #a s1 s2 =
  (length s1 = length s2
   /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))

let rec eq_i' (#a:eqtype) (s1:seq a) (s2:seq a{length s1 == length s2}) (i:nat{i <= length s1})
: Tot (r:bool{r <==> (forall j. (j >= i /\ j < length s1) ==> (index s1 j = index s2 j))})
  (decreases (length s1 - i))
= if i = length s1 then true
  else
    if index s1 i = index s2 i then eq_i' s1 s2 (i + 1)
    else false

let eq_i = eq_i'

let eq #_ s1 s2 = if length s1 = length s2 then eq_i s1 s2 0 else false

let lemma_eq_intro #_ s1 s2 = ()

let lemma_eq_refl #_ s1 s2  = ()

let lemma_eq_elim #_ s1 s2  =
  assert ( length s1 == List.length (MkSeq?.l s1) );
  assert ( length s2 == List.length (MkSeq?.l s2) );
  assert ( forall (i: nat) . i < length s1 ==> index s1 i == List.index (MkSeq?.l s1) i);
  assert ( forall (i: nat) . i < length s1 ==> index s2 i == List.index (MkSeq?.l s2) i);
  List.index_extensionality (MkSeq?.l s1) (MkSeq?.l s2)

(* Properties of [append] *)

let append_assoc #a s1 s2 s3 = List.append_assoc (MkSeq?.l s1) (MkSeq?.l s2) (MkSeq?.l s3)

let append_empty_l #a s = List.append_nil_l (MkSeq?.l s)

let append_empty_r #a s = List.append_l_nil (MkSeq?.l s)


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

let init_index #_ len contents =
  if len = 0 then () else init_index_aux len 0 contents

let init_index_ #_ len contents j = init_index len contents

private
let rec init_ghost_index_aux (#a:Type) (len:nat) (k:nat{k < len}) (contents:(i:nat { i < len } -> GTot a))
  : Lemma (requires True)
    (ensures (forall (i:nat{i < len - k}).index (init_aux_ghost len k contents) i == contents (k + i)))
    (decreases (len - k))
=
  if k + 1 = len
  then ()
  else begin
    init_ghost_index_aux #a len (k+1) contents ;
    assert (forall (i:nat{i < len - k}).
      if i = 0 then index (init_aux_ghost len k contents) 0 == contents k
      else index (init_aux_ghost len k contents) i == index (init_aux_ghost len (k+1) contents) (i-1))
  end

let init_ghost_index #_ len contents =
  if len = 0 then () else init_ghost_index_aux len 0 contents

let init_ghost_index_ #_ len contents j = init_ghost_index len contents

let lemma_equal_instances_implies_equal_types () = ()

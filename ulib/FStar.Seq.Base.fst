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
module List = FStar.List.Tot

/// The main type
type seq (a:Type) =
  | MkSeq: l:list a -> seq a

/// Isomorphic to list
let reveal #a (MkSeq l) = l
let hide #a l = MkSeq l
let reveal_hide #a l = ()
let hide_reveal #a l = ()

/// With decidable equality
let seq_hasEq a = ()

/// Eliminators: length, index, equal
let length #a (MkSeq l) = List.length l
let index  #a (MkSeq l) i = List.index l i
let equal  #a s1 s2 =
    let _ = () in
    length s1 = length s2 /\
    (forall (i:nat{i < length s1}).{:pattern (s1.(i)); (s2.(i))}
                             s1.(i) == s2.(i))

/// Auxiliary, private functions
let cons #a (x:a) (s:seq a) = MkSeq (x::MkSeq?.l s)
let hd #a (s:seq a{length s <> 0}) = List.hd (MkSeq?.l s)
let tl #a (s:seq a{length s <> 0}) = MkSeq (List.tl (MkSeq?.l s))

/// Introduction forms
let empty #a = MkSeq []

let rec create #a len v =
    if len = 0
    then MkSeq []
    else cons v (create (len - 1) v)

let rec init' #a (i:nat) (len:nat{i <= len}) (contents:(i:nat{i < len} -> a))
  : Tot (seq a) (decreases (len - i))
  = if i = len
    then MkSeq []
    else cons (contents i) (init' (i + 1) len contents)
let init #a = init' #a 0

let of_list #a l = MkSeq l

(** Creating sequences from other sequences *)

let rec update'
    (#a:Type)
    (s:seq a)
    (i:nat{i < length s})
    (v:a)
  : Tot (seq a) (decreases i)
  = if i = 0
    then cons v (tl s)
    else cons (hd s) (update' (tl s) (i - 1) v)
let update #a = update' #a

let append #a (MkSeq l1) (MkSeq l2) = MkSeq (l1 @ l2)

let rec sub'
    (#a:Type)
    (s:seq a)
    (i:nat)
    (j:nat{i <= j && j <= length s})
  : Tot (seq a) (decreases (length s))
  = if i > 0
    then sub' (tl s) (i - 1) (j - 1)
    else if j = 0
    then MkSeq []
    else cons (hd s) (sub' (tl s) i (j - 1))
let sub #a = sub' #a

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about length
////////////////////////////////////////////////////////////////////////////////
let rec length_create #a n i =
    if n = 0 then () else length_create #a (n - 1) i

let rec length_init'
    (#a:Type)
    (i:nat)
    (n:nat{i<=n})
    (v:(i:nat{i<n} -> a))
  : Lemma
    (ensures (length (init' i n v) == n - i))
    (decreases (n - i))
    [SMTPat (length (init' i n v))]
  = if i = n then () else length_init' #a (i + 1) n v
let length_init #a = length_init' #a 0

let length_of_list #a l = ()

let rec length_update #a n v s =
    if n = 0
    then ()
    else length_update #a (n - 1) v (tl s)

let length_append #a (MkSeq l1) (MkSeq l2) =
    List.append_length l1 l2

let rec length_sub'
    (#a:Type)
    (s:seq a)
    (i:nat)
    (j:nat{i <= j && j <= length s})
  : Lemma
    (ensures (length (slice s i j) = j - i)) (decreases (length s))
  = if i > 0 then length_sub' #a (tl s) (i - 1) (j - 1)
    else if j = 0 then ()
    else length_sub' #a (tl s) i (j - 1)
let length_sub #a = length_sub' #a

////////////////////////////////////////////////////////////////////////////////
/// Lemmas about index
////////////////////////////////////////////////////////////////////////////////
let rec index_create #a n v i =
    if n = 0 then ()
    else if i = 0 then ()
    else index_create #a (n - 1) v (i - 1)

let rec index_init'
    (#a:Type)
    (j:nat)
    (n:nat{j<=n})
    (v:(i:nat{i<n} -> a))
    (i:nat{i < (n - j)})
  : Lemma
    (ensures ((init' j n v).(i) == v (i + j)))
    (decreases (n - j))
  = if j = n then ()
    else if i = 0 then ()
    else index_init' (j + 1) n v (i - 1)
let index_init #a = index_init' #a 0

let index_of_list #a l i = ()

let rec index_update_here'
    (#a:Type)
    (s:seq a)
    (i:nat{i < length s})
    (v:a)
  : Lemma
    (ensures (s.(i) <- v).(i) == v)
    (decreases (length s))
  = if i = 0 then ()
    else index_update_here' (tl s) (i - 1) v
let index_update_here #a = index_update_here' #a

let rec index_update_there'
    (#a:Type)
    (s:seq a)
    (j:nat{j < length s})
    (v:a)
    (i:nat{i <> j /\ i < length s})
  : Lemma
    (ensures (s.(j) <- v).(i) == s.(i))
    (decreases (length s))
  = if i <> 0 && j <> 0
    then index_update_there' #a (tl s) (j - 1) v (i - 1)
let index_update_there #a = index_update_there' #a

let rec index_append_left'
    (#a:Type)
    (s1:seq a)
    (s2:seq a)
    (i:nat{i < length s1})
  : Lemma
    (ensures (s1 @| s2).(i) == s1.(i))
    (decreases (length s1))
  = if i <> 0 then index_append_left' #a (tl s1) s2 (i - 1)
let index_append_left #a = index_append_left' #a

let rec index_append_right'
    (#a:Type)
    (s1:seq a)
    (s2:seq a)
    (i:nat{length s1 <= i /\ i < length s1 + length s2})
  : Lemma
    (ensures (s1 @| s2).(i) == s2.(i - length s1))
    (decreases (length s1))
  =  if length s1 <> 0 then index_append_right' #a (tl s1) s2 (i - 1)
let index_append_right #a = index_append_right' #a

let rec index_sub'
    (#a:Type)
    (s:seq a)
    (i:nat)
    (j:nat{i <= j /\ j <= length s})
    (k:nat{k < j - i})
  : Lemma
    (ensures (sub s i j).(k) == s.(k + i))
    (decreases (length s))
  = if i > 0 then index_sub' (tl s) (i - 1) (j - 1) k
    else if j <> 0 && k <> 0 then index_sub' (tl s) i (j - 1) (k - 1)
let index_sub #a = index_sub' #a

////////////////////////////////////////////////////////////////////////////////
/// Extensional equality/
////////////////////////////////////////////////////////////////////////////////

let equal_intro #a s1 s2 = ()

let equal_elim #a s1 s2  =
  let MkSeq l1 = s1 in
  let MkSeq l2 = s2 in
  assert (List.length l1 == List.length l2);
  assert (forall (i:nat{i<List.length l1}).{:pattern (List.index l1 i)}
            List.index l1 i == index s1 i);
  assert (forall (i:nat{i<List.length l2}).{:pattern (List.index l2 i)}
            List.index l2 i == index s2 i);
  assert (forall (i:nat{i<List.length l2}).{:pattern (index s1 i)}
            index s1 i == index s2 i);
  List.index_extensionality l1 l2

let equal_refl #a s1 s2 = ()

////////////////////////////////////////////////////////////////////////////////
/// Revealing certain operations are isomorphic to their operations on lists
////////////////////////////////////////////////////////////////////////////////
let reveal_length #a s = ()
let reveal_index #a s i = ()
let reveal_append #a s1 s2 = ()

// (* Properties of [append] *)

// abstract let append_assoc
//   (#a: Type)
//   (s1 s2 s3: seq a)
// : Lemma
//   (ensures (append (append s1 s2) s3 == append s1 (append s2 s3)))
// = List.append_assoc (MkSeq?.l s1) (MkSeq?.l s2) (MkSeq?.l s3)

// abstract let append_empty_l
//   (#a: Type)
//   (s: seq a)
// : Lemma
//   (ensures (append createEmpty s == s))
// = List.append_nil_l (MkSeq?.l s)

// abstract let append_empty_r
//   (#a: Type)
//   (s: seq a)
// : Lemma
//   (ensures (append s createEmpty == s))
// = List.append_l_nil (MkSeq?.l s)

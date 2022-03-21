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

module LowStar.Vector


(**
 * This module provides support for mutable, partially filled arrays
 * whose contents may grow up to some fixed capacity determined
 * during initialization.
 *
 * Vectors support an insertion operation that may, if the capacity
 * has been reached, involve copying its contents to a new
 * vector of twice the capacity (so long as the capacity has not
 * already reached max_uint32).
 *
 * Conversely, an operation called `flush` is also provided to
 * shrink a vector to some prefix of its current contents.
 *
 * Other operations are fairly standard, and involve reading,
 * writing, and iterating over a vector.
 *
 *)

open FStar.Integers
open LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

type uint32_t = UInt32.t

val max_uint32: uint32_t
let max_uint32 = 4294967295ul // UInt32.uint_to_t (UInt.max_int UInt32.n)

module U32 = FStar.UInt32

/// Abstract vector type

inline_for_extraction noeq type vector_str a =
| Vec: sz:uint32_t ->
       cap:uint32_t{cap >= sz} ->
       vs:B.buffer a{B.len vs = cap} ->
       vector_str a

val vector (a: Type0): Tot Type0
let vector a = vector_str a

/// Specification

val as_seq:
  HS.mem -> #a:Type -> vec:vector a ->
  GTot (s:S.seq a{S.length s = U32.v (Vec?.sz vec)})
let as_seq h #a vec =
  B.as_seq h (B.gsub (Vec?.vs vec) 0ul (Vec?.sz vec))

/// Capacity

inline_for_extraction val size_of: #a:Type -> vec:vector a -> Tot uint32_t
inline_for_extraction let size_of #a vec =
  Vec?.sz vec

inline_for_extraction val capacity_of: #a:Type -> vec:vector a -> Tot uint32_t
inline_for_extraction let capacity_of #a vec =
  Vec?.cap vec

val is_empty: #a:Type -> vec:vector a -> Tot bool
let is_empty #a vec =
  size_of vec = 0ul

val is_full: #a:Type -> vstr:vector_str a -> GTot bool
let is_full #a vstr =
  Vec?.sz vstr >= max_uint32

/// Memory-related

val live: #a:Type -> HS.mem -> vector a -> GTot Type0
let live #a h vec =
  B.live h (Vec?.vs vec)

val freeable: #a:Type -> vector a -> GTot Type0
let freeable #a vec =
  B.freeable (Vec?.vs vec)

val loc_vector: #a:Type -> vector a -> GTot loc
let loc_vector #a vec =
  B.loc_buffer (Vec?.vs vec)

val loc_addr_of_vector: #a:Type -> vector a -> GTot loc
let loc_addr_of_vector #a vec =
  B.loc_addr_of_buffer (Vec?.vs vec)

val loc_vector_within:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  GTot loc (decreases (U32.v (j - i)))
let rec loc_vector_within #a vec i j =
  if i = j then loc_none
  else loc_union (B.loc_buffer (B.gsub (Vec?.vs vec) i 1ul))
                 (loc_vector_within vec (i + 1ul) j)

val loc_vector_within_includes_:
  #a:Type -> vec:vector a ->
  i:uint32_t ->
  j1:uint32_t{i <= j1 && j1 <= size_of vec} ->
  j2:uint32_t{i <= j2 && j2 <= j1} ->
  Lemma (requires True)
        (ensures (loc_includes (loc_vector_within vec i j1)
                               (loc_vector_within vec i j2)))
        (decreases (U32.v (j1 - i)))
let rec loc_vector_within_includes_ #a vec i j1 j2 =
  if i = j1 then ()
  else if i = j2 then ()
  else begin
    loc_vector_within_includes_ vec (i + 1ul) j1 j2;
    loc_includes_union_l (B.loc_buffer (B.gsub (Vec?.vs vec) i 1ul))
                         (loc_vector_within vec (i + 1ul) j1)
                         (loc_vector_within vec (i + 1ul) j2);
    loc_includes_union_r (loc_vector_within vec i j1)
                         (B.loc_buffer (B.gsub (Vec?.vs vec) i 1ul))
                         (loc_vector_within vec (i + 1ul) j2)
  end

val loc_vector_within_includes:
  #a:Type -> vec:vector a ->
  i1:uint32_t -> j1:uint32_t{i1 <= j1 && j1 <= size_of vec} ->
  i2:uint32_t{i1 <= i2} -> j2:uint32_t{i2 <= j2 && j2 <= j1} ->
  Lemma (requires True)
        (ensures (loc_includes (loc_vector_within vec i1 j1)
                               (loc_vector_within vec i2 j2)))
        (decreases (U32.v (j1 - i1)))
let rec loc_vector_within_includes #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else if i1 = i2 then loc_vector_within_includes_ vec i1 j1 j2
  else begin
    loc_vector_within_includes vec (i1 + 1ul) j1 i2 j2;
    loc_includes_union_l (B.loc_buffer (B.gsub (Vec?.vs vec) i1 1ul))
                         (loc_vector_within vec (i1 + 1ul) j1)
                         (loc_vector_within vec i2 j2)
  end

val loc_vector_within_included:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  Lemma (requires True)
        (ensures (loc_includes (loc_vector vec)
                               (loc_vector_within vec i j)))
        (decreases (U32.v (j - i)))
let rec loc_vector_within_included #a vec i j =
  if i = j then ()
  else loc_vector_within_included vec (i + 1ul) j

val loc_vector_within_disjoint_:
  #a:Type -> vec:vector a ->
  i1:uint32_t ->
  i2:uint32_t{i1 < i2} ->
  j2:uint32_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
        (ensures (loc_disjoint (B.loc_buffer (B.gsub (Vec?.vs vec) i1 1ul))
                               (loc_vector_within vec i2 j2)))
        (decreases (U32.v (j2 - i2)))
let rec loc_vector_within_disjoint_ #a vec i1 i2 j2 =
  if i2 = j2 then ()
  else loc_vector_within_disjoint_ vec i1 (i2 + 1ul) j2

val loc_vector_within_disjoint:
  #a:Type -> vec:vector a ->
  i1:uint32_t -> j1:uint32_t{i1 <= j1 && j1 <= size_of vec} ->
  i2:uint32_t{j1 <= i2} -> j2:uint32_t{i2 <= j2 && j2 <= size_of vec} ->
  Lemma (requires True)
        (ensures (loc_disjoint (loc_vector_within vec i1 j1)
                               (loc_vector_within vec i2 j2)))
        (decreases (U32.v (j1 - i1)))
let rec loc_vector_within_disjoint #a vec i1 j1 i2 j2 =
  if i1 = j1 then ()
  else (loc_vector_within_disjoint_ vec i1 i2 j2;
       loc_vector_within_disjoint vec (i1 + 1ul) j1 i2 j2)

val loc_vector_within_union_rev:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i < j && j <= size_of vec} ->
  Lemma (requires True)
        (ensures (loc_vector_within vec i j ==
                 loc_union (loc_vector_within vec i (j - 1ul))
                           (loc_vector_within vec (j - 1ul) j)))
        (decreases (U32.v (j - i)))
let rec loc_vector_within_union_rev #a vec i j =
  if i = j - 1ul then ()
  else begin
    loc_vector_within_union_rev vec (i + 1ul) j;
    loc_union_assoc (B.loc_buffer (B.gsub (Vec?.vs vec) i 1ul))
                    (loc_vector_within vec (i + 1ul) (j - 1ul))
                    (loc_vector_within vec (j - 1ul) j)
  end

unfold val frameOf: #a:Type -> vector a -> Tot HS.rid
unfold let frameOf #a vec =
  B.frameOf (Vec?.vs vec)

unfold val hmap_dom_eq: h0:HS.mem -> h1:HS.mem -> GTot Type0
unfold let hmap_dom_eq h0 h1 =
  Set.equal (Map.domain (HS.get_hmap h0))
            (Map.domain (HS.get_hmap h1))

val modifies_as_seq:
  #a:Type -> vec:vector a -> dloc:loc ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
                  loc_disjoint (loc_vector vec) dloc /\
                  modifies dloc h0 h1))
        (ensures (live h1 vec /\
                 as_seq h0 vec == as_seq h1 vec))
        [SMTPat (live h0 vec);
        SMTPat (loc_disjoint (loc_vector vec) dloc);
        SMTPat (modifies dloc h0 h1)]
let modifies_as_seq #a vec dloc h0 h1 =
  B.modifies_buffer_elim (Vec?.vs vec) dloc h0 h1

val modifies_as_seq_within:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
                  loc_disjoint (loc_vector_within vec i j) dloc /\
                  modifies dloc h0 h1))
        (ensures (S.slice (as_seq h0 vec) (U32.v i) (U32.v j) ==
                 S.slice (as_seq h1 vec) (U32.v i) (U32.v j)))
        (decreases (U32.v (j - i)))
        [SMTPat (live h0 vec);
        SMTPat (loc_disjoint (loc_vector_within vec i j) dloc);
        SMTPat (modifies dloc h0 h1)]
let rec modifies_as_seq_within #a vec i j dloc h0 h1 =
  if i = j then ()
  else begin
    B.modifies_buffer_elim (B.gsub (Vec?.vs vec) i 1ul) dloc h0 h1;
    modifies_as_seq_within vec (i + 1ul) j dloc h0 h1;
    assert (S.equal (S.slice (as_seq h0 vec) (U32.v i) (U32.v j))
                    (S.append (S.slice (as_seq h0 vec) (U32.v i) (U32.v i + 1))
                              (S.slice (as_seq h0 vec) (U32.v i + 1) (U32.v j))));
    assert (S.equal (S.slice (as_seq h1 vec) (U32.v i) (U32.v j))
                    (S.append (S.slice (as_seq h1 vec) (U32.v i) (U32.v i + 1))
                              (S.slice (as_seq h1 vec) (U32.v i + 1) (U32.v j))))
  end

/// Construction

inline_for_extraction val alloc_empty:
  a:Type -> Tot (vec:vector a{size_of vec = 0ul})
inline_for_extraction let alloc_empty a =
  Vec 0ul 0ul B.null

val alloc_empty_as_seq_empty:
  a:Type -> h:HS.mem ->
  Lemma (S.equal (as_seq h (alloc_empty a)) S.empty)
        [SMTPat (as_seq h (alloc_empty a))]
let alloc_empty_as_seq_empty a h = ()

val alloc_rid:
  #a:Type -> len:uint32_t{len > 0ul} -> v:a ->
  rid:HS.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
         (requires (fun h0 -> true))
         (ensures (fun h0 vec h1 ->
           frameOf vec = rid /\
           live h1 vec /\ freeable vec /\
           modifies loc_none h0 h1 /\
           Set.equal (Map.domain (HS.get_hmap h0))
                     (Map.domain (HS.get_hmap h1)) /\
           size_of vec = len /\
           S.equal (as_seq h1 vec) (S.create (U32.v len) v) /\
           B.fresh_loc (loc_vector vec) h0 h1))
let alloc_rid #a len v rid =
  Vec len len (B.malloc rid v len)

// Allocate a vector with the length `len`, filled with the initial value `v`.
// Note that the vector is allocated in the root region.
val alloc:
  #a:Type -> len:uint32_t{len > 0ul} -> v:a ->
  HST.ST (vector a)
         (requires (fun h0 -> true))
         (ensures (fun h0 vec h1 ->
           frameOf vec = HS.root /\
           live h1 vec /\ freeable vec /\
           modifies loc_none h0 h1 /\
           Set.equal (Map.domain (HS.get_hmap h0))
                     (Map.domain (HS.get_hmap h1)) /\
           size_of vec = len /\
           S.equal (as_seq h1 vec) (S.create (U32.v len) v) /\
           B.fresh_loc (loc_vector vec) h0 h1))
let alloc #a len v =
  alloc_rid len v HS.root

// Allocate a vector with the _capacity_ `len`; we still need to provide an
// initial value `ia` in order to allocate space.
val alloc_reserve:
  #a:Type -> len:uint32_t{len > 0ul} -> ia:a ->
  rid:HS.rid{HST.is_eternal_region rid} ->
  HST.ST (vector a)
         (requires (fun h0 -> true))
         (ensures (fun h0 vec h1 ->
           frameOf vec = rid /\ live h1 vec /\ freeable vec /\
           modifies loc_none h0 h1 /\
           B.fresh_loc (loc_vector vec) h0 h1 /\
           Set.equal (Map.domain (HS.get_hmap h0))
                     (Map.domain (HS.get_hmap h1)) /\
           size_of vec = 0ul /\
           S.equal (as_seq h1 vec) S.empty))
let alloc_reserve #a len ia rid =
  Vec 0ul len (B.malloc rid ia len)

// Allocate a vector with a given buffer with the length `len`.
// Note that it does not copy the buffer content; instead it directly uses the
// buffer pointer.
val alloc_by_buffer:
  #a:Type -> len:uint32_t{len > 0ul} ->
  buf:B.buffer a{B.len buf = len} ->
  HST.ST (vector a)
         (requires (fun h0 -> B.live h0 buf))
         (ensures (fun h0 vec h1 ->
           frameOf vec = B.frameOf buf /\ loc_vector vec == B.loc_buffer buf /\
           live h1 vec /\ h0 == h1 /\
           size_of vec = len /\
           S.equal (as_seq h1 vec) (B.as_seq h0 buf)))
let alloc_by_buffer #a len buf =
  Vec len len buf

/// Destruction

val free:
  #a:Type -> vec:vector a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ freeable vec))
    (ensures (fun h0 _ h1 -> modifies (loc_addr_of_vector vec) h0 h1))
let free #a vec =
  B.free (Vec?.vs vec)

/// Element access

val get:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t{i < size_of vec} -> GTot a
let get #a h vec i =
  S.index (as_seq h vec) (U32.v i)

val index:
  #a:Type -> vec:vector a -> i:uint32_t ->
  HST.ST a
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) (U32.v i) == v))
let index #a vec i =
  B.index (Vec?.vs vec) i

val front:
  #a:Type -> vec:vector a{size_of vec > 0ul} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) 0 == v))
let front #a vec =
  B.index (Vec?.vs vec) 0ul

val back:
  #a:Type -> vec:vector a{size_of vec > 0ul} ->
  HST.ST a
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\ S.index (as_seq h1 vec) (U32.v (size_of vec) - 1) == v))
let back #a vec =
  B.index (Vec?.vs vec) (size_of vec - 1ul)

/// Operations

val clear:
  #a:Type -> vec:vector a ->
  Tot (cvec:vector a{size_of cvec = 0ul})
let clear #a vec =
  Vec 0ul (Vec?.cap vec) (Vec?.vs vec)

val clear_as_seq_empty:
  #a:Type -> h:HS.mem -> vec:vector a ->
  Lemma (S.equal (as_seq h (clear vec)) S.empty)
        [SMTPat (as_seq h (clear vec))]
let clear_as_seq_empty #a h vec = ()

private val slice_append:
  #a:Type -> s:S.seq a ->
  i:nat -> j:nat{i <= j} -> k:nat{j <= k && k <= S.length s} ->
  Lemma (S.equal (S.slice s i k)
                 (S.append (S.slice s i j) (S.slice s j k)))
private let slice_append #a s i j k = ()

val assign:
  #a:Type -> vec:vector a ->
  i:uint32_t -> v:a ->
  HST.ST unit
    (requires (fun h0 -> live h0 vec /\ i < size_of vec))
    (ensures (fun h0 _ h1 ->
      hmap_dom_eq h0 h1 /\
      modifies (loc_vector_within #a vec i (i + 1ul)) h0 h1 /\
      get h1 vec i == v /\
      S.equal (as_seq h1 vec) (S.upd (as_seq h0 vec) (U32.v i) v) /\
      live h1 vec))
#reset-options "--z3rlimit 10"
let assign #a vec i v =
  let hh0 = HST.get () in
  // NOTE: `B.upd (Vec?.vs vec) i v` makes more sense,
  //       but the `modifies` postcondition is coarse-grained.
  B.upd (B.sub (Vec?.vs vec) i 1ul) 0ul v;
  let hh1 = HST.get () in
  loc_vector_within_disjoint vec 0ul i i (i + 1ul);
  modifies_as_seq_within
    vec 0ul i (loc_vector_within #a vec i (i + 1ul)) hh0 hh1;
  loc_vector_within_disjoint vec i (i + 1ul) (i + 1ul) (size_of vec);
  modifies_as_seq_within
    vec (i + 1ul) (size_of vec) (loc_vector_within #a vec i (i + 1ul)) hh0 hh1;
  slice_append (as_seq hh1 vec) 0 (U32.v i) (U32.v i + 1);
  slice_append (as_seq hh1 vec) 0 (U32.v i + 1) (U32.v (size_of vec));
  slice_append (S.upd (as_seq hh0 vec) (U32.v i) v) 0 (U32.v i) (U32.v i + 1);
  slice_append (S.upd (as_seq hh0 vec) (U32.v i) v) 0 (U32.v i + 1) (U32.v (size_of vec))

private val resize_ratio: uint32_t
private let resize_ratio = 2ul

private val new_capacity: cap:uint32_t -> Tot uint32_t
private let new_capacity cap =
  if cap >= max_uint32 / resize_ratio then max_uint32
  else if cap = 0ul then 1ul
  else cap * resize_ratio

val insert:
  #a:Type -> vec:vector a -> v:a ->
  HST.ST (vector a)
    (requires (fun h0 ->
      live h0 vec /\ freeable vec /\ not (is_full vec) /\
      HST.is_eternal_region (frameOf vec)))
    (ensures (fun h0 nvec h1 ->
      frameOf vec = frameOf nvec /\
      hmap_dom_eq h0 h1 /\
      live h1 nvec /\ freeable nvec /\
      modifies (loc_union (loc_addr_of_vector vec)
                          (loc_vector nvec)) h0 h1 /\
      size_of nvec = size_of vec + 1ul /\
      get h1 nvec (size_of vec) == v /\
      S.equal (as_seq h1 nvec) (S.snoc (as_seq h0 vec) v)))
#reset-options "--z3rlimit 20"
let insert #a vec v =
  let sz = Vec?.sz vec in
  let cap = Vec?.cap vec in
  let vs = Vec?.vs vec in
  if sz = cap
  then (let ncap = new_capacity cap in
       let nvs = B.malloc (B.frameOf vs) v ncap in
       B.blit vs 0ul nvs 0ul sz;
       B.upd nvs sz v;
       B.free vs;
       Vec (sz + 1ul) ncap nvs)
  else
    (B.upd vs sz v;
    Vec (sz + 1ul) cap vs)

// Flush elements in the vector until the index `i`.
// It also frees the original allocation and reallocates a smaller space for
// remaining elements.
val flush:
  #a:Type -> vec:vector a -> ia:a ->
  i:uint32_t{i <= size_of vec} ->
  HST.ST (vector a)
    (requires (fun h0 ->
      live h0 vec /\ freeable vec /\
      HST.is_eternal_region (frameOf vec)))
    (ensures (fun h0 fvec h1 ->
      frameOf vec = frameOf fvec /\
      hmap_dom_eq h0 h1 /\
      live h1 fvec /\ freeable fvec /\
      modifies (loc_union (loc_addr_of_vector vec)
                          (loc_vector fvec)) h0 h1 /\
      size_of fvec = size_of vec - i /\
      S.equal (as_seq h1 fvec)
              (S.slice (as_seq h0 vec) (U32.v i) (U32.v (size_of vec)))))
let flush #a vec ia i =
  let fsz = Vec?.sz vec - i in
  let asz = if Vec?.sz vec = i then 1ul else fsz in
  let vs = Vec?.vs vec in
  let fvs = B.malloc (B.frameOf vs) ia asz in
  B.blit vs i fvs 0ul fsz;
  B.free vs;
  Vec fsz asz fvs

val shrink:
  #a:Type -> vec:vector a ->
  new_size:uint32_t{new_size <= size_of vec} ->
  Tot (vector a)
let shrink #a vec new_size =
  Vec new_size (Vec?.cap vec) (Vec?.vs vec)
  

/// Iteration

val fold_left_seq:
  #a:Type -> #b:Type0 -> seq:S.seq a ->
  f:(b -> a -> GTot b) -> ib:b ->
  GTot b (decreases (S.length seq))
let rec fold_left_seq #a #b seq f ib =
  if S.length seq = 0 then ib
  else fold_left_seq (S.tail seq) f (f ib (S.head seq))

val fold_left_buffer:
  #a:Type -> #b:Type0 -> len:uint32_t ->
  buf:B.buffer a{B.len buf = len} ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> B.live h0 buf))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (B.as_seq h0 buf) f ib))
    (decreases (B.length buf))
let rec fold_left_buffer #a #b len buf f ib =
  if len = 0ul then ib
  else (fold_left_buffer (len - 1ul) (B.sub buf 1ul (len - 1ul))
                         f (f ib (B.index buf 0ul)))

val fold_left:
  #a:Type -> #b:Type0 -> vec:vector a ->
  f:(b -> a -> Tot b) -> ib:b ->
  HST.ST b
    (requires (fun h0 -> live h0 vec))
    (ensures (fun h0 v h1 ->
      h0 == h1 /\
      v == fold_left_seq (as_seq h0 vec) f ib))
let fold_left #a #b vec f ib =
  fold_left_buffer (Vec?.sz vec) (B.sub (Vec?.vs vec) 0ul (Vec?.sz vec)) f ib

val forall_seq:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_seq #a seq i j p =
  forall (idx:nat{i <= idx && idx < j}).
    p (S.index seq idx)

val forall_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  i:nat -> j:nat{i <= j && j <= B.length buf} ->
  p:(a -> GTot Type0) -> GTot Type0
let forall_buffer #a h buf i j p =
  forall_seq (B.as_seq h buf) i j p

val forall_:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_ #a h vec i j p =
  forall_seq (as_seq h vec) (U32.v i) (U32.v j) p

val forall_all:
  #a:Type -> h:HS.mem -> vec:vector a ->
  p:(a -> Tot Type0) -> GTot Type0
let forall_all #a h vec p =
  forall_ h vec 0ul (size_of vec) p

val forall2_seq:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_seq #a seq i j p =
  forall (k:nat{i <= k && k < j}) (l:nat{i <= l && l < j && k <> l}).
    p (S.index seq k) (S.index seq l)

val forall2_buffer:
  #a:Type -> h:HS.mem -> buf:B.buffer a ->
  i:nat -> j:nat{i <= j && j <= B.length buf} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_buffer #a h buf i j p =
  forall2_seq (B.as_seq h buf) i j p

val forall2:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2 #a h vec i j p =
  forall2_seq (as_seq h vec) (U32.v i) (U32.v j) p

val forall2_all:
  #a:Type -> h:HS.mem -> vec:vector a ->
  p:(a -> a -> GTot Type0) -> GTot Type0
let forall2_all #a h vec p =
  forall2 h vec 0ul (size_of vec) p

/// Facts

val get_as_seq_index:
  #a:Type -> h:HS.mem -> buf:B.buffer a -> i:uint32_t{i < B.len buf} ->
  Lemma (B.get h buf (U32.v i) == S.index (B.as_seq h (B.gsub buf i 1ul)) 0)
let get_as_seq_index #a h buf i = ()

val get_preserved:
  #a:Type -> vec:vector a ->
  i:uint32_t{i < size_of vec} ->
  p:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
                  loc_disjoint p (loc_vector_within vec i (i + 1ul)) /\
                  modifies p h0 h1))
        (ensures (get h0 vec i == get h1 vec i))
let get_preserved #a vec i p h0 h1 =
  get_as_seq_index h0 (Vec?.vs vec) i;
  get_as_seq_index h1 (Vec?.vs vec) i

private val get_preserved_within:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  k:uint32_t{(k < i || j <= k) && k < size_of vec} ->
  h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
                  modifies (loc_vector_within vec i j) h0 h1))
        (ensures (get h0 vec k == get h1 vec k))
        [SMTPat (live h0 vec);
        SMTPat (modifies (loc_vector_within vec i j) h0 h1);
        SMTPat (get h0 vec k)]
let get_preserved_within #a vec i j k h0 h1 =
  if k < i then begin
    loc_vector_within_disjoint vec k (k + 1ul) i j;
    get_preserved vec k (loc_vector_within vec i j) h0 h1
  end
  else begin
    loc_vector_within_disjoint vec i j k (k + 1ul);
    get_preserved vec k (loc_vector_within vec i j) h0 h1
  end

val forall_seq_ok:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  k:nat{i <= k && k < j} ->
  p:(a -> GTot Type0) ->
  Lemma (requires (forall_seq seq i j p))
        (ensures (p (S.index seq k)))
let forall_seq_ok #a seq i j k p = ()

val forall2_seq_ok:
  #a:Type -> seq:S.seq a ->
  i:nat -> j:nat{i <= j && j <= S.length seq} ->
  k:nat{i <= k && k < j} -> l:nat{i <= l && l < j && k <> l} ->
  p:(a -> a -> GTot Type0) ->
  Lemma (requires (forall2_seq seq i j p))
        (ensures (p (S.index seq k) (S.index seq l)))
let forall2_seq_ok #a seq i j k l p = ()

val forall_as_seq:
  #a:Type -> s0:S.seq a -> s1:S.seq a{S.length s0 = S.length s1} ->
  i:nat -> j:nat{i <= j && j <= S.length s0} ->
  k:nat{i <= k && k < j} ->
  p:(a -> Tot Type0) ->
  Lemma (requires (p (S.index s0 k) /\ S.slice s0 i j == S.slice s1 i j))
        (ensures (p (S.index s1 k)))
        [SMTPat (p (S.index s0 k));
         SMTPat (S.slice s0 i j);
         SMTPat (S.slice s1 i j)]
let forall_as_seq #a s0 s1 i j k p =
  assert (S.index (S.slice s0 i j) (k - i) ==
         S.index (S.slice s1 i j) (k - i))

val forall_preserved:
  #a:Type -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  p:(a -> Tot Type0) ->
  dloc:loc -> h0:HS.mem -> h1:HS.mem ->
  Lemma (requires (live h0 vec /\
                  loc_disjoint (loc_vector_within vec i j) dloc /\
                  forall_ h0 vec i j p /\
                  modifies dloc h0 h1))
        (ensures (forall_ h1 vec i j p))
let forall_preserved #a vec i j p dloc h0 h1 =
  modifies_as_seq_within vec i j dloc h0 h1;
  assert (S.slice (as_seq h0 vec) (U32.v i) (U32.v j) ==
         S.slice (as_seq h1 vec) (U32.v i) (U32.v j))

val forall2_extend:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j < size_of vec} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p /\
                  forall_ h vec i j
                    (fun a -> p a (get h vec j) /\ p (get h vec j) a)))
        (ensures (forall2 h vec i (j + 1ul) p))
let forall2_extend #a h vec i j p = ()

val forall2_forall_left:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  k:uint32_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
        (ensures (forall_ h vec i k (p (get h vec k))))
let forall2_forall_left #a h vec i j k p = ()

val forall2_forall_right:
  #a:Type -> h:HS.mem -> vec:vector a ->
  i:uint32_t -> j:uint32_t{i <= j && j <= size_of vec} ->
  k:uint32_t{i <= k && k < j} ->
  p:(a -> a -> Tot Type0) ->
  Lemma (requires (forall2 h vec i j p))
        (ensures (forall_ h vec (k + 1ul) j (p (get h vec k))))
let forall2_forall_right #a h vec i j k p = ()

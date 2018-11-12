module Slice

open FStar.Seq
// TODO: this is only for truncate_slice, which could probably be replaced with
// truncated_slice, possibly needing an SMTPat
open FStar.HyperStack
open FStar.HyperStack.ST
module B = FStar.Buffer
module U32 = FStar.UInt32

type byte = FStar.UInt8.byte
type bytes = seq byte

(*** Slices: buffers with runtime length *)

// a byte buffer type indexed by size
type lbuffer (len: nat) = b:B.buffer byte{B.length b == len}

// augment a buffer with a runtime length
noeq type bslice =
  | BSlice : len:U32.t -> p:lbuffer (U32.v len) -> bslice

let live h (b: bslice) = B.live h b.p
let as_seq h (b: bslice) : Ghost (s:bytes{length s == U32.v b.len})
  (requires (live h b))
  (ensures (fun _ -> True)) = B.as_seq h b.p

let advance_slice (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) : bslice =
  BSlice (U32.sub b.len off) (B.sub b.p off (U32.sub b.len off))

let advance_slice_spec (b:bslice) (off:U32.t{U32.v off <= U32.v b.len}) h :
  Lemma (requires (live h b))
        (ensures (live h (advance_slice b off) /\
                  as_seq h (advance_slice b off) == slice (as_seq h b) (U32.v off) (length (as_seq h b))))
  = ()

let u32_add_overflows (a b:U32.t) : overflow:bool{not overflow <==> U32.v a + U32.v b < pow2 32} =
  U32.lt (U32.add_mod a b) a

val truncate_slice : b:bslice -> len:U32.t{U32.v len <= U32.v b.len} -> Stack bslice
  (requires (fun h0 -> live h0 b))
  (ensures (fun h0 r h1 -> live h1 b /\
                        live h1 r /\
                        h0 == h1 /\
                        as_seq h1 r == slice (as_seq h1 b) 0 (U32.v len)))
let truncate_slice b len = BSlice len (B.sub b.p (U32.uint_to_t 0) len)

// pure version of truncate_slice (which is in Stack)
val truncated_slice : b:bslice -> len:U32.t{U32.v len <= U32.v b.len} -> bslice
let truncated_slice b len = BSlice len (B.sub b.p (U32.uint_to_t 0) len)

let preorder (rel: 'a -> 'a -> Type0) =
    (forall x. rel x x) /\
    (forall x y z. rel x y /\ rel y x ==> rel x z)

let bslice_prefix (b b':bslice) : GTot Type0 =
    // B.includes x y means x is the larger buffer
    B.includes b'.p b.p /\
    B.idx b.p + B.length b.p == B.idx b'.p + B.length b'.p

val bslice_prefix_equals (b b': bslice) (h0 h1:mem) :
    Lemma (requires (live h0 b' /\
                    live h1 b' /\
                    as_seq h0 b' == as_seq h1 b' /\
                    bslice_prefix b b'))
          (ensures (live h0 b /\
                    live h1 b /\
                    as_seq h0 b = as_seq h1 b))
          [SMTPat (bslice_prefix b b'); SMTPat (as_seq h0 b'); SMTPat (as_seq h1 b')]
let bslice_prefix_equals b b' h0 h1 =
    B.includes_as_seq h0 h1 b'.p b.p

let bslice_prefix_trans (x y z: bslice) :
    Lemma (requires (bslice_prefix x y /\ bslice_prefix y z))
          (ensures (bslice_prefix x z)) = ()

(*! Framing slices *)

val modifies_slice : b:bslice -> h:mem -> h':mem -> GTot Type0
let modifies_slice b h h' =
  B.modifies_1 b.p h h'

let modifies_prefix (b:bslice) (len:U32.t{U32.v len <= U32.v b.len}) =
  modifies_slice (truncated_slice b len)

let u32_max (a b:U32.t) : max:U32.t{U32.lte a max /\ U32.lte b max} =
  if U32.gt a b then a else b

let modifies_prefix_plus (b:bslice) (len1 len2: (off:U32.t{U32.v off <= U32.v b.len})) h h' h''
  : Lemma (requires (modifies_prefix b len1 h h' /\
                     modifies_prefix b len2 h' h''))
          (ensures (modifies_prefix b (u32_max len1 len2) h h'')) =
  B.lemma_reveal_modifies_1 (truncated_slice b len1).p h h';
  B.lemma_reveal_modifies_1 (truncated_slice b len2).p h' h'';
  B.lemma_intro_modifies_1 (truncated_slice b (u32_max len1 len2)).p h h'';
  ()

let modifies_prefix_times (b:bslice) (len1: U32.t) (len2: U32.t{U32.v len1 + U32.v len2 <= U32.v b.len}) h h' h''
  : Lemma (requires (U32.v len1 + U32.v len2 < pow2 32 /\
                     modifies_prefix b len1 h h' /\
                     modifies_prefix (advance_slice b len1) len2 h' h''))
          (ensures (modifies_prefix b (U32.add len1 len2) h h'')) =
  B.lemma_reveal_modifies_1 (truncated_slice b len1).p h h';
  B.lemma_reveal_modifies_1 (truncated_slice (advance_slice b len1) len2).p h' h'';
  B.lemma_intro_modifies_1 (truncated_slice b (U32.add len1 len2)).p h h'';
  ()

// similar to B.includes, but no restriction on indices (and thus an
// equivalence)
let same_ref (#a:Type) (b1 b2:B.buffer a) =
    B.frameOf b1 == B.frameOf b2 /\
    B.max_length b1 == B.max_length b2 /\
    B.content b1 === B.content b2

// XXX: why is this not in the standard library?
let same_ref_equivalence (#a:Type) :
    Lemma ((forall b. same_ref #a b b) /\
           (forall b1 b2. same_ref #a b1 b2 ==> same_ref b2 b1) /\
           (forall b1 b2 b3. same_ref #a b1 b2 ==> same_ref b2 b3 ==> same_ref b1 b3)) = ()

// b2 starts exactly after b1 ends (for the same underlying ref)
let buffers_adjacent (#a:Type) (b1 b2:B.buffer a) : Type0 =
    same_ref b1 b2 /\
    B.idx b2 == B.idx b1 + B.length b1

let is_concat_of (#a:Type) (b b1 b2:B.buffer a) : Type0 =
    same_ref b b1 /\
    same_ref b b2 /\
    buffers_adjacent b1 b2 /\
    B.idx b1 == B.idx b /\
    B.length b1 + B.length b2 == B.length b

let is_concat_liveness (#a:Type) (b b1 b2:B.buffer a) h :
    Lemma (requires (is_concat_of b b1 b2 /\ B.live h b))
          (ensures (B.live h b <==> B.live h b1 /\ B.live h b2)) = ()

let is_concat_disjoint (#a:Type) (b b1 b2:B.buffer a) :
    Lemma (requires (is_concat_of b b1 b2))
          (ensures (B.disjoint b1 b2)) = ()

let is_concat_append (#a:Type) (b b1 b2:B.buffer a) h :
    Lemma (requires (is_concat_of b b1 b2 /\
                     B.live h b))
          (ensures (B.live h b /\
                    B.live h b1 /\
                    B.live h b2 /\
                    B.as_seq h b == B.as_seq h b1 `append` B.as_seq h b2)) =
    lemma_eq_intro (B.as_seq h b) (B.as_seq h b1 `append` B.as_seq h b2)

let is_concat_suffix (#a:Type) (b b1 b2:B.buffer a) h :
    Lemma (requires (is_concat_of b b1 b2 /\
                     B.live h b))
          (ensures (B.live h b /\
                    B.live h b2 /\
                    // just to satisfy the bounds in the refinements to slice
                    B.length b1 + B.length b2 == B.length b /\
                    B.as_seq h b2 == slice (B.as_seq h b) (B.length b1) (B.length b))) =
    lemma_eq_intro (B.as_seq h b2) (slice (B.as_seq h b) (B.length b1) (B.length b))

let is_concat_prefix (#a:Type) (b b1 b2:B.buffer a) h :
    Lemma (requires (is_concat_of b b1 b2 /\
                     B.live h b))
          (ensures (B.live h b /\
                    B.live h b1 /\
                    // just to satisfy the bounds in the refinements to slice
                    B.length b1 + B.length b2 == B.length b /\
                    B.as_seq h b1 == slice (B.as_seq h b) 0 (B.length b1))) =
    lemma_eq_intro (B.as_seq h b1) (slice (B.as_seq h b) 0 (B.length b1))

(*! Splitting buffers *)

(** This single primitive is sufficient to encode many useful patterns, and
because it always creates disjoint slices it tends to have much easier framing
than the general [B.sub]. *)

// general split_at primitive (think of Rust's slice::split_at_mut)
// polymorphic: inline and hope that it type-checks in kremlin
[@"substitute"]
val buffer_split_at: #a:Type -> b:B.buffer a ->
    off:U32.t{U32.v off <= B.length b} ->
    // TODO: this shouldn't be necessary, but Buffer provides no way to advance
    // a pointer without specifying a new length
    // TODO: the above is wrong, there's B.offset to do exactly what we want for
    // the second buffer
    len:U32.t{U32.v len == B.length b} ->
    Pure (B.buffer a * B.buffer a)
         (requires True)
         (ensures (fun r ->
                     let (b1, b2) = r in
                     is_concat_of b b1 b2 /\
                     B.length b1 == U32.v off))
[@"substitute"]
let buffer_split_at #a b off len =
    (B.sub b 0ul off, B.sub b off (U32.sub len off))

val bslice_split_at: b:bslice -> off:U32.t{U32.v off <= U32.v b.len} ->
    Pure (bslice * bslice)
         (requires True)
         (ensures (fun r->
                     let (b1, b2) = r in
                     is_concat_of b.p b1.p b2.p /\
                     b1.len == off /\
                     U32.v b2.len == U32.v b.len - U32.v off))
let bslice_split_at b off =
    let (b1, b2) = buffer_split_at b.p off b.len in
    (BSlice off b1, BSlice (U32.sub b.len off) b2)

// TODO: this proof is somewhat tricky; it boils down to any buffer disjoint to
// truncated_slice is either some other underlying storage or a subset of
// advance_slice, and we've assumed that the advance slices are equal
val modifies_prefix_seq_intro (b:bslice) (len: U32.t{U32.v len <= U32.v b.len}) (h0 h1:mem) :
  Lemma (requires (modifies_slice b h0 h1 /\
                   live h0 b /\
                   live h1 b /\
                   begin
                    let len = U32.v len in
                    let s0 = as_seq h0 b in
                    let s1 = as_seq h1 b in
                    forall (i:nat{len <= i /\ i < U32.v b.len}).{:pattern (index s0 i); (index s1 i)}
                                                                 (index s0 i == index s1 i)
                   end))
        (ensures (modifies_prefix b len h0 h1))
let modifies_prefix_seq_intro b len h0 h1 =
  B.lemma_reveal_modifies_1 b.p h0 h1;
  admit();
  B.lemma_intro_modifies_1 (truncated_slice b len).p h0 h1

val modifies_prefix_split (b b1 b2:bslice) (len: U32.t{U32.v len <= U32.v b.len}) (h0 h1:mem) :
    Lemma (requires (live h0 b /\
                     live h1 b /\
                     is_concat_of b.p b1.p b2.p /\
                     modifies_slice b1 h0 h1))
          (ensures (is_concat_of b.p b1.p b2.p /\
                    modifies_prefix b b1.len h0 h1))
let modifies_prefix_split b b1 b2 len h0 h1 =
  is_concat_append b.p b1.p b2.p h1;
  admit();
  // TODO: this is probably the right proof strategy, but maybe can do a
  // lower-level proof
  modifies_prefix_seq_intro b b1.len h0 h1;
  ()

// modifies_slice b1 ==> modifies_slice (b1+b2)
let modifies_grow_from_b1 (b b1 b2:bslice) (h0 h1:mem) : Lemma
    (requires (live h0 b /\ live h1 b /\
              is_concat_of b.p b1.p b2.p /\
              modifies_slice b1 h0 h1))
    (ensures (modifies_slice b h0 h1)) =
    B.modifies_subbuffer_1 h0 h1 b1.p b.p

// modifies_slice b2 ==> modifies_slice (b1+b2)
let modifies_grow_from_b2 (b b1 b2:bslice) (h0 h1:mem) : Lemma
    (requires (live h0 b /\ live h1 b /\
              is_concat_of b.p b1.p b2.p /\
              modifies_slice b2 h0 h1))
    (ensures (modifies_slice b h0 h1)) =
    B.modifies_subbuffer_1 h0 h1 b2.p b.p

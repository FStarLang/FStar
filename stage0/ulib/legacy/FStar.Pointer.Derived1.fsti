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
module FStar.Pointer.Derived1
include FStar.Pointer.Base

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

val includes_gfield_gen
  (#t: typ)
  (p: pointer t)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (includes p q))
  (ensures (includes p (gfield q fd)))
  [SMTPat (includes p (gfield q fd))]

val includes_gufield_gen
  (#t: typ)
  (p: pointer t)
  (#l: union_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (includes p q))
  (ensures (includes p (gufield q fd)))
  [SMTPat (includes p (gufield q fd))]

val includes_gcell_gen
  (#t: typ)
  (p: pointer t)
  (#length: array_length_t)
  (#value: typ)
  (q: pointer (TArray length value))
  (i: UInt32.t)
: Lemma
  (requires (includes p q /\ UInt32.v i < UInt32.v length))
  (ensures (UInt32.v i < UInt32.v length /\ includes p (gcell q i)))
  [SMTPat (includes p (gcell q i))]

val loc_includes_union_assoc_r2l
  (s1 s2 s3 s: loc)
: Lemma
  (requires (loc_includes (loc_union s1 (loc_union s2 s3)) s))
  (ensures (loc_includes (loc_union (loc_union s1 s2) s3) s))
  [SMTPat (loc_includes (loc_union (loc_union s1 s2) s3) s)]

val loc_includes_union_assoc_l2r
  (s1 s2 s3 s: loc)
: Lemma
  (requires (loc_includes (loc_union (loc_union s1 s2) s3) s))
  (ensures (loc_includes (loc_union s1 (loc_union s2 s3)) s))
  [SMTPat (loc_includes (loc_union s1 (loc_union s2 s3)) s)]

val loc_includes_union_assoc_focalize_1
  (l1 l2 x r s: loc)
: Lemma
  (requires (loc_includes (loc_union (loc_union l1 l2) (loc_union x r)) s))
  (ensures (loc_includes (loc_union l1 (loc_union (loc_union l2 x) r)) s))
  [SMTPat (loc_includes (loc_union l1 (loc_union (loc_union l2 x) r)) s)]

val loc_includes_union_assoc_focalize_2
  (l x r1 r2 s: loc)
: Lemma
  (requires (loc_includes (loc_union l (loc_union x (loc_union r1 r2))) s))
  (ensures (loc_includes (loc_union l (loc_union (loc_union x r1) r2)) s))
  [SMTPat (loc_includes (loc_union l (loc_union (loc_union x r1) r2)) s)]

val loc_includes_region_union_r
  (l: loc)
  (s1 s2: Set.set HH.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union l (loc_regions s1)) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union l (loc_regions s1)) (loc_regions s2))]

val loc_includes_region_union_assoc
  (l r: loc)
  (s1 s2: Set.set HH.rid)
: Lemma
  (requires (loc_includes (loc_union l r)) (loc_regions (Set.intersect s2 (Set.complement s1))))
  (ensures (loc_includes (loc_union l (loc_union (loc_regions s1) r)) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union l (loc_union (loc_regions s1) r)) (loc_regions s2))]

val loc_disjoint_none_l
  (s: loc)
: Lemma
  (ensures (loc_disjoint loc_none s))
  [SMTPat (loc_disjoint loc_none s)]

val loc_disjoint_union_l
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s /\ loc_disjoint s2 s))
  (ensures (loc_disjoint (loc_union s1 s2) s))
  [SMTPat (loc_disjoint (loc_union s1 s2) s)]

val loc_disjoint_gfield_r
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint p (loc_pointer q)))
  (ensures (loc_disjoint p (loc_pointer (gfield q fd))))
  [SMTPat (loc_disjoint p (loc_pointer (gfield q fd)))]

val loc_disjoint_gfield_l
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint (loc_pointer q) p))
  (ensures (loc_disjoint (loc_pointer (gfield q fd)) p))
  [SMTPat (loc_disjoint (loc_pointer (gfield q fd)) p)]

val loc_disjoint_gufield_r
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint p (loc_pointer q)))
  (ensures (loc_disjoint p (loc_pointer (gufield q fd))))
  [SMTPat (loc_disjoint p (loc_pointer (gufield q fd)))]

val loc_disjoint_gufield_l
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint (loc_pointer q) p))
  (ensures (loc_disjoint (loc_pointer (gufield q fd)) p))
  [SMTPat (loc_disjoint (loc_pointer (gufield q fd)) p)]

val loc_disjoint_gcell_r
  (p: loc)
  (#value: typ)
  (#len: array_length_t)
  (q: pointer (TArray len value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v len /\ loc_disjoint p (loc_pointer q)))
  (ensures (UInt32.v i < UInt32.v len /\ loc_disjoint p (loc_pointer (gcell q i))))
  [SMTPat (loc_disjoint p (loc_pointer (gcell q i)))]

val loc_disjoint_gcell_l
  (p: loc)
  (#value: typ)
  (#len: array_length_t)
  (q: pointer (TArray len value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v len /\ loc_disjoint (loc_pointer q) p))
  (ensures (UInt32.v i < UInt32.v len /\ loc_disjoint (loc_pointer (gcell q i)) p))
  [SMTPat (loc_disjoint (loc_pointer (gcell q i)) p)]

val loc_disjoint_gsingleton_buffer_of_pointer_r
  (l: loc)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_disjoint l (loc_pointer p)))
  (ensures (loc_disjoint l (loc_buffer (gsingleton_buffer_of_pointer p))))
  [SMTPat (loc_disjoint l (loc_buffer (gsingleton_buffer_of_pointer p)))]

val loc_disjoint_gsingleton_buffer_of_pointer_l
  (l: loc)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_disjoint (loc_pointer p) l))
  (ensures (loc_disjoint (loc_buffer (gsingleton_buffer_of_pointer p)) l))
  [SMTPat (loc_disjoint (loc_buffer (gsingleton_buffer_of_pointer p)) l)]

val loc_disjoint_gbuffer_of_array_pointer_r
  (l: loc)
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires (loc_disjoint l (loc_pointer p)))
  (ensures (loc_disjoint l (loc_buffer (gbuffer_of_array_pointer p))))
  [SMTPat (loc_disjoint l (loc_buffer (gbuffer_of_array_pointer p)))]

val loc_disjoint_gbuffer_of_array_pointer_l
  (l: loc)
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires (loc_disjoint (loc_pointer p) l))
  (ensures (loc_disjoint (loc_buffer (gbuffer_of_array_pointer p)) l))
  [SMTPat (loc_disjoint (loc_buffer (gbuffer_of_array_pointer p)) l)]

val loc_disjoint_gpointer_of_buffer_cell_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i))))
  [SMTPat (loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i)))]

val loc_disjoint_gpointer_of_buffer_cell_l
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer b) l))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l))
  [SMTPat (loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l)]

val loc_disjoint_gsub_buffer_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer (gsub_buffer b i len))))
  [SMTPat (loc_disjoint l (loc_buffer (gsub_buffer b i len)))]

val loc_disjoint_gsub_buffer_l
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer b) l))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer (gsub_buffer b i len)) l))
  [SMTPat (loc_disjoint (loc_buffer (gsub_buffer b i len)) l)]

val loc_disjoint_addresses_pointer
  (#t: typ)
  (p: pointer t)
  (r: HH.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> frameOf p \/ (~ (Set.mem (as_addr p) n))))
  (ensures (loc_disjoint (loc_addresses r n) (loc_pointer p)))
  [SMTPat (loc_disjoint (loc_addresses r n) (loc_pointer p))]

val loc_disjoint_union_r_elim
  (l l1 l2: loc)
: Lemma
  (requires (loc_disjoint l (loc_union l1 l2)))
  (ensures (loc_disjoint l l1 /\ loc_disjoint l l2))
  [SMTPat (loc_disjoint l (loc_union l1 l2))]

val loc_disjoint_union_l_elim
  (l l1 l2: loc)
: Lemma
  (requires (loc_disjoint (loc_union l1 l2) l))
  (ensures (loc_disjoint l1 l /\ loc_disjoint l2 l))
  [SMTPat (loc_disjoint (loc_union l1 l2) l)]

val modifies_trans_incl_l
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3 /\ loc_includes s12 s23))
  (ensures (modifies s12 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

val modifies_trans_incl_r
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3 /\ loc_includes s23 s12))
  (ensures (modifies s23 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

val modifies_fresh_frame_popped'
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_regions (Set.singleton (HS.get_tip h1))) s) h1 h2 /\
    (HS.get_tip h2) == (HS.get_tip h1) /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    (HS.get_tip h3) == HS.get_tip h0
  ))

val buffer_includes_gsub_r_gen
  (#t: typ)
  (b0: buffer t)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_includes b0 b
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_includes b0 (gsub_buffer b i len)
  ))
  [SMTPat (buffer_includes b0 (gsub_buffer b i len))]

val readable_gpointer_of_buffer_cell_gsub
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (j: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v i <= UInt32.v j /\
    UInt32.v j < UInt32.v i + UInt32.v len /\
    buffer_readable h (gsub_buffer b i len)
  ))
  (ensures (
    UInt32.v j < UInt32.v (buffer_length b) /\
    readable h (gpointer_of_buffer_cell b j)
  ))
  [SMTPat (readable h (gpointer_of_buffer_cell b j)); SMTPat (buffer_readable h (gsub_buffer b i len))]

val buffer_contents_equal
  (#a: typ)
  (b1 b2: buffer a)
  (len: UInt32.t)
: HST.Stack bool
  (requires (fun h ->
    hasEq (type_of_typ a) /\
    UInt32.v len <= UInt32.v (buffer_length b1) /\
    UInt32.v len <= UInt32.v (buffer_length b2) /\
    buffer_readable h (gsub_buffer b1 0ul len) /\
    buffer_readable h (gsub_buffer b2 0ul len)
  ))
  (ensures (fun h0 z h1 ->
    h1 == h0 /\
    UInt32.v len <= UInt32.v (buffer_length b1) /\
    UInt32.v len <= UInt32.v (buffer_length b2) /\
    (z == true <==> Seq.equal (buffer_as_seq h0 (gsub_buffer b1 0ul len)) (buffer_as_seq h0 (gsub_buffer b2 0ul len)))
  ))

val buffer_readable_intro_empty
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
: Lemma
  (requires (
    buffer_live h b /\
    UInt32.v (buffer_length b) == 0
  ))
  (ensures (buffer_readable h b))
  [SMTPatOr [
    [SMTPat (buffer_readable h b)];
    [SMTPat (buffer_live h b)];
  ]]

val loc_disjoint_gsub_buffer_gpointer_of_buffer_cell
  (#a: typ)
  (b: buffer a)
  (i: UInt32.t)
  (len: UInt32.t)
  (j: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v j < UInt32.v (buffer_length b) /\
    (UInt32.v j < UInt32.v i \/ UInt32.v i + UInt32.v len <= UInt32.v j)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    UInt32.v j < UInt32.v (buffer_length b) /\
    loc_disjoint (loc_buffer (gsub_buffer b i len)) (loc_pointer (gpointer_of_buffer_cell b j))
  ))
  [SMTPat (loc_disjoint (loc_buffer (gsub_buffer b i len)) (loc_pointer (gpointer_of_buffer_cell b j)))]

val buffer_readable_gsub_intro
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_live h b /\ (
     forall (j: UInt32.t) .
     (UInt32.v i <= UInt32.v j /\
     UInt32.v j < UInt32.v i + UInt32.v len) ==>
     readable h (gpointer_of_buffer_cell b j)
  )))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\  
    buffer_readable h (gsub_buffer b i len)
  ))

val buffer_readable_gsub_elim
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\  
    buffer_readable h (gsub_buffer b i len)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_live h b /\ (
     forall (j: UInt32.t) .
     (UInt32.v i <= UInt32.v j /\
     UInt32.v j < UInt32.v i + UInt32.v len) ==>
     readable h (gpointer_of_buffer_cell b j)
  )))

val buffer_as_seq_gsub_buffer_append
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len1: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len1 + UInt32.v len2 <= UInt32.v (buffer_length b)
//    buffer_readable h (gsub_buffer b i (UInt32.add len1 len2))
  ))
  (ensures (
    UInt32.v i + UInt32.v len1 + UInt32.v len2 <= UInt32.v (buffer_length b) /\
    buffer_as_seq h (gsub_buffer b i (UInt32.add len1 len2)) == Seq.append (buffer_as_seq h (gsub_buffer b i len1)) (buffer_as_seq h (gsub_buffer b (UInt32.add i len1) len2))
  ))

val buffer_as_seq_gsub_buffer_snoc
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    buffer_as_seq h (gsub_buffer b i (UInt32.add len 1ul)) == Seq.snoc (buffer_as_seq h (gsub_buffer b i len)) (Seq.index (buffer_as_seq h b) (UInt32.v i + UInt32.v len))
  ))

val buffer_as_seq_gsub_buffer_cons
  (#t: typ)
  (h: HS.mem)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b)
  ))
  (ensures (
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    buffer_as_seq h (gsub_buffer b i (UInt32.add len 1ul)) == Seq.cons (Seq.index (buffer_as_seq h b) (UInt32.v i)) (buffer_as_seq h (gsub_buffer b (UInt32.add i 1ul) len))
  ))

val buffer_snoc
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (v: type_of_typ t)
: HST.Stack unit
  (requires (fun h ->
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    buffer_readable h (gsub_buffer b i len)
  ))
  (ensures (fun h _ h' ->
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    modifies (loc_pointer (gpointer_of_buffer_cell b (UInt32.add i len))) h h' /\
    buffer_readable h' (gsub_buffer b i (UInt32.add len 1ul)) /\
    buffer_as_seq h' (gsub_buffer b i (UInt32.add len 1ul)) == Seq.snoc (buffer_as_seq h (gsub_buffer b i len)) v
  ))

val buffer_cons
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (v: type_of_typ t)
: HST.Stack unit
  (requires (fun h ->
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    buffer_readable h (gsub_buffer b (UInt32.add i 1ul) len)
  ))
  (ensures (fun h _ h' ->
    UInt32.v i + UInt32.v len < UInt32.v (buffer_length b) /\
    modifies (loc_pointer (gpointer_of_buffer_cell b i)) h h' /\
    buffer_readable h' (gsub_buffer b i (UInt32.add len 1ul)) /\
    buffer_as_seq h' (gsub_buffer b i (UInt32.add len 1ul)) == Seq.cons v (buffer_as_seq h (gsub_buffer b (UInt32.add i 1ul) len))
  ))

val buffer_readable_gsub_merge
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h: HS.mem)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_readable h (gsub_buffer b 0ul i) /\
    buffer_readable h (gsub_buffer b i len) /\ (
    let off = UInt32.add i len in
    buffer_readable h (gsub_buffer b off (UInt32.sub (buffer_length b) off))
  )))
  (ensures (buffer_readable h b))

val buffer_readable_modifies_gsub
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
  (h0 h1: HS.mem)
  (l: loc)
: Lemma
  (requires (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    modifies l h0 h1 /\
    loc_disjoint l (loc_buffer (gsub_buffer b 0ul i)) /\
    loc_disjoint l (loc_buffer (gsub_buffer b (UInt32.add i len) (UInt32.sub (buffer_length b) (UInt32.add i len)))) /\
    buffer_readable h0 b /\
    buffer_readable h1 (gsub_buffer b i len)
  ))
  (ensures (
    UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_readable h1 b
  ))

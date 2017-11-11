module FStar.Pointer
include FStar.Pointer.Base

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open HST // for := , !

let includes_gfield_gen
  (#t: typ)
  (p: pointer t)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (includes p q))
  (ensures (includes p (gfield q fd)))
  [SMTPat (includes p (gfield q fd))]
= includes_gfield q fd;
  includes_trans p q (gfield q fd)

let includes_gufield_gen
  (#t: typ)
  (p: pointer t)
  (#l: union_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (includes p q))
  (ensures (includes p (gufield q fd)))
  [SMTPat (includes p (gufield q fd))]
= includes_gufield q fd;
  includes_trans p q (gufield q fd)

let includes_gcell_gen
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
= includes_gcell q i;
  includes_trans p q (gcell q i)

let loc_includes_union_assoc_r2l
  (s1 s2 s3 s: loc)
: Lemma
  (requires (loc_includes (loc_union s1 (loc_union s2 s3)) s))
  (ensures (loc_includes (loc_union (loc_union s1 s2) s3) s))
  [SMTPat (loc_includes (loc_union (loc_union s1 s2) s3) s)]
= loc_includes_trans (loc_union (loc_union s1 s2) s3) (loc_union s1 (loc_union s2 s3)) s

let loc_includes_union_assoc_l2r
  (s1 s2 s3 s: loc)
: Lemma
  (requires (loc_includes (loc_union (loc_union s1 s2) s3) s))
  (ensures (loc_includes (loc_union s1 (loc_union s2 s3)) s))
  [SMTPat (loc_includes (loc_union s1 (loc_union s2 s3)) s)]
= loc_includes_trans (loc_union s1 (loc_union s2 s3)) (loc_union (loc_union s1 s2) s3) s

let loc_includes_union_assoc_focalize_1
  (l1 l2 x r s: loc)
: Lemma
  (requires (loc_includes (loc_union (loc_union l1 l2) (loc_union x r)) s))
  (ensures (loc_includes (loc_union l1 (loc_union (loc_union l2 x) r)) s))
  [SMTPat (loc_includes (loc_union l1 (loc_union (loc_union l2 x) r)) s)]
= loc_includes_trans (loc_union l1 (loc_union (loc_union l2 x) r)) (loc_union (loc_union l1 l2) (loc_union x r)) s

let loc_includes_union_assoc_focalize_2
  (l x r1 r2 s: loc)
: Lemma
  (requires (loc_includes (loc_union l (loc_union x (loc_union r1 r2))) s))
  (ensures (loc_includes (loc_union l (loc_union (loc_union x r1) r2)) s))
  [SMTPat (loc_includes (loc_union l (loc_union (loc_union x r1) r2)) s)]
= loc_includes_trans (loc_union l (loc_union (loc_union x r1) r2)) (loc_union l (loc_union x (loc_union r1 r2))) s

let loc_includes_region_union_r
  (l: loc)
  (s1 s2: Set.set HH.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union l (loc_regions s1)) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union l (loc_regions s1)) (loc_regions s2))]
= loc_includes_trans (loc_union l (loc_regions s1)) (loc_union (loc_regions s1) l) (loc_regions s2)

let loc_includes_region_union_assoc
  (l r: loc)
  (s1 s2: Set.set HH.rid)
: Lemma
  (requires (loc_includes (loc_union l r)) (loc_regions (Set.intersect s2 (Set.complement s1))))
  (ensures (loc_includes (loc_union l (loc_union (loc_regions s1) r)) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union l (loc_union (loc_regions s1) r)) (loc_regions s2))]
= loc_includes_trans (loc_union l (loc_union (loc_regions s1) r)) (loc_union (loc_regions s1) (loc_union l r)) (loc_regions s2)

let loc_disjoint_none_l
  (s: loc)
: Lemma
  (ensures (loc_disjoint loc_none s))
  [SMTPat (loc_disjoint loc_none s)]
= loc_disjoint_none_r s;
  loc_disjoint_sym s loc_none

let loc_disjoint_union_l
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s /\ loc_disjoint s2 s))
  (ensures (loc_disjoint (loc_union s1 s2) s))
  [SMTPat (loc_disjoint (loc_union s1 s2) s)]
= loc_disjoint_sym s1 s;
  loc_disjoint_sym s2 s;
  loc_disjoint_union_r s s1 s2;
  loc_disjoint_sym s (loc_union s1 s2)

let loc_disjoint_gfield_r
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint p (loc_pointer q)))
  (ensures (loc_disjoint p (loc_pointer (gfield q fd))))
  [SMTPat (loc_disjoint p (loc_pointer (gfield q fd)))]
= loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gfield q fd))

let loc_disjoint_gfield_l
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TStruct l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint (loc_pointer q) p))
  (ensures (loc_disjoint (loc_pointer (gfield q fd)) p))
  [SMTPat (loc_disjoint (loc_pointer (gfield q fd)) p)]
= loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gfield_r p q fd;
  loc_disjoint_sym p (loc_pointer (gfield q fd))

let loc_disjoint_gufield_r
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint p (loc_pointer q)))
  (ensures (loc_disjoint p (loc_pointer (gufield q fd))))
  [SMTPat (loc_disjoint p (loc_pointer (gufield q fd)))]
= loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gufield q fd))

let loc_disjoint_gufield_l
  (p: loc)
  (#l: struct_typ)
  (q: pointer (TUnion l))
  (fd: struct_field l)
: Lemma
  (requires (loc_disjoint (loc_pointer q) p))
  (ensures (loc_disjoint (loc_pointer (gufield q fd)) p))
  [SMTPat (loc_disjoint (loc_pointer (gufield q fd)) p)]
= loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gufield_r p q fd;
  loc_disjoint_sym p (loc_pointer (gufield q fd))

let loc_disjoint_gcell_r
  (p: loc)
  (#value: typ)
  (#len: array_length_t)
  (q: pointer (TArray len value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v len /\ loc_disjoint p (loc_pointer q)))
  (ensures (UInt32.v i < UInt32.v len /\ loc_disjoint p (loc_pointer (gcell q i))))
  [SMTPat (loc_disjoint p (loc_pointer (gcell q i)))]
= loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gcell q i))

let loc_disjoint_gcell_l
  (p: loc)
  (#value: typ)
  (#len: array_length_t)
  (q: pointer (TArray len value))
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v len /\ loc_disjoint (loc_pointer q) p))
  (ensures (UInt32.v i < UInt32.v len /\ loc_disjoint (loc_pointer (gcell q i)) p))
  [SMTPat (loc_disjoint (loc_pointer (gcell q i)) p)]
= loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gcell_r p q i;
  loc_disjoint_sym p (loc_pointer (gcell q i))

let loc_disjoint_gsingleton_buffer_of_pointer_r
  (l: loc)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_disjoint l (loc_pointer p)))
  (ensures (loc_disjoint l (loc_buffer (gsingleton_buffer_of_pointer p))))
  [SMTPat (loc_disjoint l (loc_buffer (gsingleton_buffer_of_pointer p)))]
= loc_disjoint_includes l (loc_pointer p) l (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_disjoint_gsingleton_buffer_of_pointer_l
  (l: loc)
  (#t: typ)
  (p: pointer t)
: Lemma
  (requires (loc_disjoint (loc_pointer p) l))
  (ensures (loc_disjoint (loc_buffer (gsingleton_buffer_of_pointer p)) l))
  [SMTPat (loc_disjoint (loc_buffer (gsingleton_buffer_of_pointer p)) l)]
= loc_disjoint_sym (loc_pointer p) l;
  loc_disjoint_gsingleton_buffer_of_pointer_r l p;
  loc_disjoint_sym l (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_disjoint_gbuffer_of_array_pointer_r
  (l: loc)
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires (loc_disjoint l (loc_pointer p)))
  (ensures (loc_disjoint l (loc_buffer (gbuffer_of_array_pointer p))))
  [SMTPat (loc_disjoint l (loc_buffer (gbuffer_of_array_pointer p)))]
= loc_disjoint_includes l (loc_pointer p) l (loc_buffer (gbuffer_of_array_pointer p))

let loc_disjoint_gbuffer_of_array_pointer_l
  (l: loc)
  (#t: typ)
  (#len: array_length_t)
  (p: pointer (TArray len t))
: Lemma
  (requires (loc_disjoint (loc_pointer p) l))
  (ensures (loc_disjoint (loc_buffer (gbuffer_of_array_pointer p)) l))
  [SMTPat (loc_disjoint (loc_buffer (gbuffer_of_array_pointer p)) l)]
= loc_disjoint_includes (loc_pointer p) l (loc_buffer (gbuffer_of_array_pointer p)) l

let loc_disjoint_gpointer_of_buffer_cell_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer b)))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i))))
  [SMTPat (loc_disjoint l (loc_pointer (gpointer_of_buffer_cell b i)))]
= loc_disjoint_includes l (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i))

let loc_disjoint_gpointer_of_buffer_cell_l
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: Lemma
  (requires (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer b) l))
  (ensures (UInt32.v i < UInt32.v (buffer_length b) /\ loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l))
  [SMTPat (loc_disjoint (loc_pointer (gpointer_of_buffer_cell b i)) l)]
= loc_disjoint_includes (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i)) l

let loc_disjoint_gsub_buffer_r
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer b)))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint l (loc_buffer (gsub_buffer b i len))))
= loc_disjoint_includes l (loc_buffer b) l (loc_buffer (gsub_buffer b i len))

let loc_disjoint_gsub_buffer_l
  (l: loc)
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer b) l))
  (ensures (UInt32.v i + UInt32.v len <= UInt32.v (buffer_length b) /\ loc_disjoint (loc_buffer (gsub_buffer b i len)) l))
= loc_disjoint_includes (loc_buffer b) l (loc_buffer (gsub_buffer b i len)) l

let loc_disjoint_addresses_pointer
  (#t: typ)
  (p: pointer t)
  (r: HH.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> frameOf p \/ (~ (Set.mem (as_addr p) n))))
  (ensures (loc_disjoint (loc_addresses r n) (loc_pointer p)))
  [SMTPat (loc_disjoint (loc_addresses r n) (loc_pointer p))]
= loc_disjoint_sym (loc_pointer p) (loc_addresses r n)

let loc_disjoint_union_r_elim
  (l l1 l2: loc)
: Lemma
  (requires (loc_disjoint l (loc_union l1 l2)))
  (ensures (loc_disjoint l l1 /\ loc_disjoint l l2))
  [SMTPat (loc_disjoint l (loc_union l1 l2))]
= loc_disjoint_includes l (loc_union l1 l2) l l1;
  loc_disjoint_includes l (loc_union l1 l2) l l2

let loc_disjoint_union_l_elim
  (l l1 l2: loc)
: Lemma
  (requires (loc_disjoint (loc_union l1 l2) l))
  (ensures (loc_disjoint l1 l /\ loc_disjoint l2 l))
  [SMTPat (loc_disjoint (loc_union l1 l2) l)]
= ()

let modifies_trans_incl_l
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3 /\ loc_includes s12 s23))
  (ensures (modifies s12 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]
= ()

let modifies_trans_incl_r
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3 /\ loc_includes s23 s12))
  (ensures (modifies s23 h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]
= ()

let modifies_fresh_frame_popped'
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_regions (Set.singleton h1.HS.tip)) s) h1 h2 /\
    h2.HS.tip == h1.HS.tip /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    h3.HS.tip == h0.HS.tip
  ))
= modifies_fresh_frame_popped h0 h1 s h2 h3

let buffer_includes_gsub_r_gen
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
= buffer_includes_gsub_r b i len;
  buffer_includes_trans b0 b (gsub_buffer b i len)

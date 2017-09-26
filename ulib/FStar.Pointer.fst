module FStar.Pointer
include FStar.Pointer.Base

module DM = FStar.DependentMap
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

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
  [SMTPat (loc_disjoint l (loc_buffer (gsub_buffer b i len)))]
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
  [SMTPat (loc_disjoint (loc_buffer (gsub_buffer b i len)) l)]
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

let readable_gpointer_of_buffer_cell_gsub
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
= assert (gpointer_of_buffer_cell b j == gpointer_of_buffer_cell (gsub_buffer b i len) (UInt32.sub j i))

(* buffer read: can be defined as a derived operation: pointer_of_buffer_cell ; read *)

abstract
val read_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
: HST.Stack (type_of_typ t)
  (requires (fun h -> UInt32.v i < UInt32.v (buffer_length b) /\ readable h (gpointer_of_buffer_cell b i)))
  (ensures (fun h v h' -> UInt32.v i < UInt32.v (buffer_length b) /\ h' == h /\ v == Seq.index (buffer_as_seq h b) (UInt32.v i)))

let read_buffer #t b i =
  read (pointer_of_buffer_cell b i)

abstract
val write_buffer
  (#t: typ)
  (b: buffer t)
  (i: UInt32.t)
  (v: type_of_typ t)
: HST.Stack unit
  (requires (fun h -> UInt32.v i < UInt32.v (buffer_length b) /\ buffer_live h b))
  (ensures (fun h _ h' ->
    UInt32.v i < UInt32.v (buffer_length b) /\
    modifies_1 (gpointer_of_buffer_cell b i) h h' /\
    modifies (loc_pointer (gpointer_of_buffer_cell b i)) h h' /\
    buffer_live h' b /\
    readable h' (gpointer_of_buffer_cell b i) /\
    Seq.index (buffer_as_seq h' b) (UInt32.v i) == v /\
    (buffer_readable h b ==> (
      buffer_readable h' b /\
      Seq.equal (buffer_as_seq h' b) (Seq.upd (buffer_as_seq h b) (UInt32.v i) v)
  ))))

let write_buffer #t b i v =
  let h = HST.get () in
  write (pointer_of_buffer_cell b i) v;
  let h' = HST.get () in
  let f () : Lemma
    (requires (buffer_readable h b))
    (ensures (buffer_readable h' b))
  = buffer_readable_intro h' b
  in
  Classical.move_requires f ()

private
let rec buffer_contents_equal_aux
  (#a: typ)
  (b1 b2: buffer a)
  (len: UInt32.t)
: HST.Stack bool
  (requires (fun h ->
    hasEq (type_of_typ a) /\
    UInt32.v len == UInt32.v (buffer_length b1) /\
    UInt32.v len == UInt32.v (buffer_length b2) /\
    buffer_readable h b1 /\
    buffer_readable h b2
  ))
  (ensures (fun h0 z h1 ->
    h1 == h0 /\
    UInt32.v len == UInt32.v (buffer_length b1) /\
    UInt32.v len == UInt32.v (buffer_length b2) /\
    (z == true <==> Seq.equal (buffer_as_seq h0 b1) (buffer_as_seq h0 b2))
  ))
  (decreases (UInt32.v len))
= if len = 0ul
  then true
  else begin
    let len' = UInt32.sub len 1ul in
    let t : eqtype = type_of_typ a in
    let r1 : t = read_buffer b1 len' in
    let r2 : t = read_buffer b2 len' in
    let b1' = sub_buffer b1 0ul len' in
    let b2' = sub_buffer b2 0ul len' in
    let h = HST.get () in
    assert (Seq.equal (buffer_as_seq h b1) (Seq.snoc (buffer_as_seq h b1') r1));
    assert (Seq.equal (buffer_as_seq h b2) (Seq.snoc (buffer_as_seq h b2') r2));
    if r1  = r2
    then
      buffer_contents_equal_aux b1' b2' len'
    else
      false
  end

abstract
let buffer_contents_equal
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
= let b1' = sub_buffer b1 0ul len in
  let b2' = sub_buffer b2 0ul len in
  buffer_contents_equal_aux b1' b2' len

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

let buffer_readable_intro_empty #t h b =
  buffer_readable_intro h b

let loc_disjoint_gsub_buffer_gpointer_of_buffer_cell
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
= assert (gpointer_of_buffer_cell b j == gpointer_of_buffer_cell (gsub_buffer b j 1ul) 0ul)

private
unfold
let copy_buffer_contents'_pre
  (#t: typ)
  (a: buffer t) (* source *)
  (b: buffer t) (* destination *)
  (len: UInt32.t)
  (h: HS.mem)
: GTot Type0
= UInt32.v len == UInt32.v (buffer_length a) /\
  UInt32.v len == UInt32.v (buffer_length b) /\
  buffer_readable h a /\
  buffer_live h b /\
  loc_disjoint (loc_buffer a) (loc_buffer b)

private
unfold
let copy_buffer_contents'_post
  (#t: typ)
  (a: buffer t) (* source *)
  (b: buffer t) (* destination *)
  (len: UInt32.t)
  (h0 h1: HS.mem)
: GTot Type0
= UInt32.v len == UInt32.v (buffer_length a) /\
  UInt32.v len == UInt32.v (buffer_length b) /\
  modifies (loc_buffer b) h0 h1 /\
  buffer_readable h1 b /\
  Seq.equal (buffer_as_seq h1 b) (buffer_as_seq h0 a)

let buffer_readable_snoc
  (#a: typ)
  (h: HS.mem)
  (b: buffer a)
: Lemma
  (requires (
    let len = buffer_length b in (
    UInt32.v len > 0 /\ (
    let len' = UInt32.sub len 1ul in (
    buffer_readable h (gsub_buffer b 0ul len') /\
    readable h (gpointer_of_buffer_cell b len')
  )))))
  (ensures (
    buffer_readable h b
  ))
= buffer_readable_intro h b

private
let copy_buffer_contents'_zero
  (#t: typ)
  (a: buffer t) (* source *)
  (b: buffer t) (* destination *)
  (len: UInt32.t)
: HST.Stack unit
  (requires (fun h ->
    copy_buffer_contents'_pre a b len h /\
    len == 0ul
  ))
  (ensures (fun h0 _ h1 ->
    copy_buffer_contents'_post a b len h0 h1
  ))
= let h = HST.get () in
  buffer_readable_intro_empty h b
  // pattern on buffer_readable_intro_empty triggers only with the ST state AND if _pre and _post are marked `unfold`

private
let copy_buffer_contents'_nonzero
  (#t: typ)
  (a: buffer t) (* source *)
  (b: buffer t) (* destination *)
  (len: UInt32.t)
  (h0: Ghost.erased HS.mem)
: HST.Stack unit
  (requires (fun h ->
    copy_buffer_contents'_pre a b len (Ghost.reveal h0) /\
    len <> 0ul /\ (
    let len' = UInt32.sub len 1ul in (
    copy_buffer_contents'_post (gsub_buffer a 0ul len') (gsub_buffer b 0ul len') len' (Ghost.reveal h0) h
  ))))
  (ensures (fun _ _ h1 ->
    copy_buffer_contents'_post a b len (Ghost.reveal h0) h1
  ))
= let len' = UInt32.sub len 1ul in
  let a' = sub_buffer a 0ul len' in
  let b' = sub_buffer b 0ul len' in
  let r = read_buffer a len' in
  write_buffer b len' r;
  let h1 = HST.get () in
  buffer_readable_snoc h1 b;
  assert (Seq.equal (buffer_as_seq h1 b) (Seq.snoc (buffer_as_seq h1 (gsub_buffer b 0ul len')) r));
  assert (Seq.equal (buffer_as_seq (Ghost.reveal h0) a) (Seq.snoc (buffer_as_seq (Ghost.reveal h0) (gsub_buffer a 0ul len')) r))

private
let rec copy_buffer_contents'
  (#t: typ)
  (a: buffer t) (* source *)
  (b: buffer t) (* destination *)
  (len: UInt32.t)
: HST.Stack unit
  (requires (fun h ->
    copy_buffer_contents'_pre a b len h
  ))
  (ensures (fun h0 _ h1 ->
    copy_buffer_contents'_post a b len h0 h1
  ))
  (decreases (UInt32.v len))
= if len = 0ul
  then
    copy_buffer_contents'_zero a b len
  else begin
    let _h0 = HST.get () in
    let h0 = Ghost.hide _h0 in
    let len' = UInt32.sub len 1ul in
    let a' = sub_buffer a 0ul len' in
    let b' = sub_buffer b 0ul len' in
    copy_buffer_contents' a' b' len' ;
    copy_buffer_contents'_nonzero a b len h0
  end

abstract
let copy_buffer_contents
  (#t: typ)
  (a: buffer t) (* source *)
  (idx_a: UInt32.t)
  (b: buffer t) (* destination *)
  (idx_b: UInt32.t)
  (len: UInt32.t)
: HST.Stack unit
  (requires (fun h ->
    UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
    UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_live h (gsub_buffer b idx_b len) /\
    buffer_readable h (gsub_buffer a idx_a len) /\
    loc_disjoint (loc_buffer (gsub_buffer a idx_a len)) (loc_buffer (gsub_buffer b idx_b len))
  ))
  (ensures (fun h0 _ h1 ->
    UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
    UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
    modifies (loc_buffer (gsub_buffer b idx_b len)) h0 h1 /\
    buffer_readable h1 (gsub_buffer b idx_b len) /\
    Seq.equal (buffer_as_seq h1 (gsub_buffer b idx_b len)) (buffer_as_seq h0 (gsub_buffer a idx_a len))
  ))
= let a' = sub_buffer a idx_a len in
  let b' = sub_buffer b idx_b len in
  copy_buffer_contents' a' b' len


(*
let h = HST.get () in
  if len = 0ul
  then begin
    buffer_readable_intro_empty h b;
    admit ()
  end else begin
    let len' = UInt32.sub len 1ul in
    assert (buffer_readable h a);
    admit ()
  (*
    let a' = sub_buffer a 0ul len' in
    let h0 = HST.get () in
    let b' = sub_buffer b 0ul len' in
    assert (buffer_readable h0 a');
    assert (buffer_live h0 b');
    assert (loc_disjoint (loc_buffer a') (loc_buffer b'));
    copy_buffer_contents' a' b' len';
//    let r = read_buffer a len' in
    let h05 = HST.get () in
    assume (buffer_live h05 b);
//    write_buffer b len' r;
    admit ()
    let h1 = HST.get () in
    assume (modifies (loc_buffer b) h0 h1);
    assume (buffer_readable h1 b);
    assume (Seq.equal (buffer_as_seq h1 b) (buffer_as_seq h0 a))
    *)
  end


(*

let rec copy_buffer_contents'
  (#t: typ)
  (a: buffer t) (* source *)
  (idx_a: UInt32.t)
  (b: buffer t) (* destination *)
  (idx_b: UInt32.t)
  (len: UInt32.t)
: HST.ST unit
  (requires (fun h ->
    UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
    UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
    buffer_readable h (gsub_buffer a idx_a len) /\
    buffer_live h b /\
    loc_disjoint (loc_buffer (gsub_buffer a idx_a len)) (loc_buffer (gsub_buffer b idx_b len))
  ))
  (ensures (fun h0 _ h1 ->
    UInt32.v idx_a + UInt32.v len <= UInt32.v (buffer_length a) /\
    UInt32.v idx_b + UInt32.v len <= UInt32.v (buffer_length b) /\
    modifies (loc_buffer (gsub_buffer b idx_b len)) h0 h1 /\
    buffer_readable h1 (gsub_buffer b idx_b len) /\
    buffer_as_seq h1 (gsub_buffer b idx_b len) == buffer_as_seq h0 (gsub_buffer a idx_a len)
  ))
  (decreases (UInt32.v len))
= if len = 0ul
  then ()
  else begin
    
  end

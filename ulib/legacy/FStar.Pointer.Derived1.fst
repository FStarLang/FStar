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

module HH = FStar.HyperStack
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let includes_gfield_gen #t p #l q fd =
  includes_gfield q fd;
  includes_trans p q (gfield q fd)

let includes_gufield_gen #t p #l q fd =
  includes_gufield q fd;
  includes_trans p q (gufield q fd)

let includes_gcell_gen #t p #length #value q i =
  includes_gcell q i;
  includes_trans p q (gcell q i)

let loc_includes_union_assoc_r2l s1 s2 s3 s =
  loc_includes_trans (loc_union (loc_union s1 s2) s3) (loc_union s1 (loc_union s2 s3)) s

let loc_includes_union_assoc_l2r s1 s2 s3 s =
  loc_includes_trans (loc_union s1 (loc_union s2 s3)) (loc_union (loc_union s1 s2) s3) s

let loc_includes_union_assoc_focalize_1 l1 l2 x r s =
  loc_includes_trans (loc_union l1 (loc_union (loc_union l2 x) r)) (loc_union (loc_union l1 l2) (loc_union x r)) s

let loc_includes_union_assoc_focalize_2 l x r1 r2 s =
  loc_includes_trans (loc_union l (loc_union (loc_union x r1) r2)) (loc_union l (loc_union x (loc_union r1 r2))) s

let loc_includes_region_union_r l s1 s2 =
  loc_includes_trans (loc_union l (loc_regions s1)) (loc_union (loc_regions s1) l) (loc_regions s2)

let loc_includes_region_union_assoc l r s1 s2 =
  loc_includes_trans (loc_union l (loc_union (loc_regions s1) r)) (loc_union (loc_regions s1) (loc_union l r)) (loc_regions s2)

let loc_disjoint_none_l s =
  loc_disjoint_none_r s;
  loc_disjoint_sym s loc_none

let loc_disjoint_union_l s s1 s2 =
  loc_disjoint_sym s1 s;
  loc_disjoint_sym s2 s;
  loc_disjoint_union_r s s1 s2;
  loc_disjoint_sym s (loc_union s1 s2)

let loc_disjoint_gfield_r p #l q fd =
  loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gfield q fd))

let loc_disjoint_gfield_l p #l q fd =
  loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gfield_r p q fd;
  loc_disjoint_sym p (loc_pointer (gfield q fd))

let loc_disjoint_gufield_r p #l q fd =
  loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gufield q fd))

let loc_disjoint_gufield_l p #l q fd =
  loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gufield_r p q fd;
  loc_disjoint_sym p (loc_pointer (gufield q fd))

let loc_disjoint_gcell_r p #value #len q i =
  loc_disjoint_includes p (loc_pointer q) p (loc_pointer (gcell q i))

let loc_disjoint_gcell_l p #value #len q i =
  loc_disjoint_sym (loc_pointer q) p;
  loc_disjoint_gcell_r p q i;
  loc_disjoint_sym p (loc_pointer (gcell q i))

let loc_disjoint_gsingleton_buffer_of_pointer_r l #t p =
  loc_disjoint_includes l (loc_pointer p) l (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_disjoint_gsingleton_buffer_of_pointer_l l #t p =
  loc_disjoint_sym (loc_pointer p) l;
  loc_disjoint_gsingleton_buffer_of_pointer_r l p;
  loc_disjoint_sym l (loc_buffer (gsingleton_buffer_of_pointer p))

let loc_disjoint_gbuffer_of_array_pointer_r l #t #len p =
  loc_disjoint_includes l (loc_pointer p) l (loc_buffer (gbuffer_of_array_pointer p))

let loc_disjoint_gbuffer_of_array_pointer_l l #t #len p =
  loc_disjoint_includes (loc_pointer p) l (loc_buffer (gbuffer_of_array_pointer p)) l

let loc_disjoint_gpointer_of_buffer_cell_r l #t b i =
  loc_disjoint_includes l (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i))

let loc_disjoint_gpointer_of_buffer_cell_l l #t b i =
  loc_disjoint_includes (loc_buffer b) l (loc_pointer (gpointer_of_buffer_cell b i)) l

let loc_disjoint_gsub_buffer_r l #t b i len =
  loc_disjoint_includes l (loc_buffer b) l (loc_buffer (gsub_buffer b i len))

let loc_disjoint_gsub_buffer_l l #t b i len =
  loc_disjoint_includes (loc_buffer b) l (loc_buffer (gsub_buffer b i len)) l

let loc_disjoint_addresses_pointer #t p r n =
  loc_disjoint_sym (loc_pointer p) (loc_addresses r n)

let loc_disjoint_union_r_elim l l1 l2 =
  loc_disjoint_includes l (loc_union l1 l2) l l1;
  loc_disjoint_includes l (loc_union l1 l2) l l2

let loc_disjoint_union_l_elim l l1 l2 = ()

let modifies_trans_incl_l s12 h1 h2 s23 h3 = ()

let modifies_trans_incl_r s12 h1 h2 s23 h3 = ()

let modifies_fresh_frame_popped' h0 h1 s h2 h3 =
  modifies_fresh_frame_popped h0 h1 s h2 h3

let buffer_includes_gsub_r_gen #t b0 b i len =
  buffer_includes_gsub_r b i len;
  buffer_includes_trans b0 b (gsub_buffer b i len)

let readable_gpointer_of_buffer_cell_gsub #t h b i len j =
  assert (gpointer_of_buffer_cell b j == gpointer_of_buffer_cell (gsub_buffer b i len) (UInt32.sub j i))

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

let buffer_contents_equal #a b1 b2 len =
  let b1' = sub_buffer b1 0ul len in
  let b2' = sub_buffer b2 0ul len in
  buffer_contents_equal_aux b1' b2' len

let buffer_readable_intro_empty #t h b =
  buffer_readable_intro h b

let loc_disjoint_gsub_buffer_gpointer_of_buffer_cell #a b i len j =
  assert (gpointer_of_buffer_cell b j == gpointer_of_buffer_cell (gsub_buffer b j 1ul) 0ul)

let buffer_readable_gsub_intro #t h b i len =
  buffer_readable_intro h (gsub_buffer b i len)

let buffer_readable_gsub_elim #t h b i len =
  buffer_readable_elim h (gsub_buffer b i len)

let buffer_as_seq_gsub_buffer_append #t h b i len1 len2 =
  Seq.lemma_eq_intro (buffer_as_seq h (gsub_buffer b i (UInt32.add len1 len2))) (Seq.append (buffer_as_seq h (gsub_buffer b i len1)) (buffer_as_seq h (gsub_buffer b (UInt32.add i len1) len2)))

let buffer_as_seq_gsub_buffer_snoc #t h b i len =
  Seq.lemma_eq_intro (buffer_as_seq h (gsub_buffer b i (UInt32.add len 1ul))) (Seq.snoc (buffer_as_seq h (gsub_buffer b i len)) (Seq.index (buffer_as_seq h b) (UInt32.v i + UInt32.v len)))

let buffer_as_seq_gsub_buffer_cons #t h b i len =
  Seq.lemma_eq_intro (buffer_as_seq h (gsub_buffer b i (UInt32.add len 1ul))) (Seq.cons (Seq.index (buffer_as_seq h b) (UInt32.v i)) (buffer_as_seq h (gsub_buffer b (UInt32.add i 1ul) len)))

let buffer_snoc #t b i len v =
  let h = HST.get () in
  buffer_readable_gsub_elim h b i len;
  write_buffer b (UInt32.add i len) v;
  let h' = HST.get () in
  buffer_readable_gsub_intro h' b i (UInt32.add len 1ul);
  buffer_as_seq_gsub_buffer_snoc h' b i len;
  assert (Seq.index (buffer_as_seq h' b) (UInt32.v (UInt32.add i len)) == v)

let buffer_cons #t b i len v =
  let h = HST.get () in
  buffer_readable_gsub_elim h b (UInt32.add i 1ul) len;
  write_buffer b i v;
  let h' = HST.get () in
  buffer_readable_gsub_intro h' b i (UInt32.add len 1ul);
  buffer_as_seq_gsub_buffer_cons h' b i len

let buffer_readable_gsub_merge #t b i len h =
  buffer_readable_intro h b

let buffer_readable_modifies_gsub #t b i len h0 h1 l =
  buffer_readable_intro h1 (gsub_buffer b 0ul i);
  buffer_readable_intro h1 (gsub_buffer b (UInt32.add i len) (UInt32.sub (buffer_length b) (UInt32.add i len)));
  buffer_readable_gsub_merge b i len h1

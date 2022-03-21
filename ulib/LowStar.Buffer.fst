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
module LowStar.Buffer

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
 * Wrapper over LowStar.Monotonic.Buffer, with trivial preorders
 *   -- functions that take explicit preorder as arguments (e.g. sub etc.)
 *   -- these include allocation functions also
 *)
let trivial_preorder (a:Type0) :srel a = fun _ _ -> True

type buffer (a:Type0) = mbuffer a (trivial_preorder a) (trivial_preorder a)

unfold let null (#a:Type0) :buffer a = mnull #a #(trivial_preorder a) #(trivial_preorder a)

unfold let gsub (#a:Type0) = mgsub #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let gsub_inj (#a:Type0) = mgsub_inj #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a) (trivial_preorder a)

[@@unifier_hint_injective]
inline_for_extraction
type pointer (a:Type0) = b:buffer a{length b == 1}

inline_for_extraction
type pointer_or_null (a:Type0) = b:buffer a{if g_is_null b then True else length b == 1}

inline_for_extraction let sub (#a:Type0) = msub #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

inline_for_extraction let offset (#a:Type0) = moffset #a #(trivial_preorder a) #(trivial_preorder a) (trivial_preorder a)

unfold let lbuffer (a:Type0) (len:nat) = lmbuffer a (trivial_preorder a) (trivial_preorder a) len

inline_for_extraction let gcmalloc (#a:Type0) = mgcmalloc #a #(trivial_preorder a)

inline_for_extraction let malloc (#a:Type0) = mmalloc #a #(trivial_preorder a)

inline_for_extraction let alloca (#a:Type0) = malloca #a #(trivial_preorder a)

inline_for_extraction let alloca_of_list (#a:Type0) = malloca_of_list #a #(trivial_preorder a)

inline_for_extraction let gcmalloc_of_list (#a:Type0) = mgcmalloc_of_list #a #(trivial_preorder a)

module L = FStar.List.Tot

unfold
let assign_list_t #a (l: list a) = (b: buffer a) -> HST.Stack unit
  (requires (fun h0 ->
    live h0 b /\
    length b = L.length l))
  (ensures (fun h0 _ h1 ->
    live h1 b /\
    (modifies (loc_buffer b) h0 h1) /\
    as_seq h1 b == Seq.seq_of_list l))

let rec assign_list #a (l: list a): assign_list_t l
= fun b ->
  Seq.lemma_seq_of_list_induction l;
  match l with
  | [] ->
      let h = HST.get () in
      assert (length b = 0);
      assert (Seq.length (as_seq h b) = 0);
      assert (Seq.equal (as_seq h b) (Seq.empty #a));
      assert (Seq.seq_of_list [] `Seq.equal` Seq.empty #a)
  | hd :: tl ->
      let b_hd = sub b 0ul 1ul in
      let b_tl = offset b 1ul in
      let h = HST.get () in
      upd b_hd 0ul hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      assert (as_seq h1 b_hd == as_seq h0 b_hd);
      assert (get h1 b_hd 0 == hd);
      assert (as_seq h1 b_tl == Seq.seq_of_list tl);
      assert (Seq.equal (as_seq h1 b) (Seq.append (as_seq h1 b_hd) (as_seq h1 b_tl)));
      assert ((Seq.seq_of_list l) == (Seq.cons hd (Seq.seq_of_list tl)))

(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Lens.Buffer
open LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.Integers

(* This module provides an instance of an `hs_lens` for monotonic
   buffers, allowing viewing a hyperstack containing a buffer as just
   a sequence of the buffer's contents.
   
   This is one of two main "leaf" instance of an `hs_lens`, since
   (almost) all mutable types in LowStar are expressed via monotonic
   buffers.

   The other one is LowStar.Lens.Pointer

   The `ref` types are an exception: for convenient use with LensST,
   we recommend using `pointer` instead of `ref`.
*)

/// `lseq_of`: A sequence whose length matches the buffer's length
let lseq_of #a #p #q (b:B.mbuffer a p q) =
  Seq.lseq a (B.length b)

/// `buffer_hs_lens`:
///   hs_lens between a buffer `b` and `lseq_of b`
let buffer_hs_lens #a #p #q (b:B.mbuffer a p q) =
  l:hs_lens (B.mbuffer a p q) (lseq_of b){
    Ghost.reveal l.footprint == B.loc_buffer b
  }

/// `reader_t l`: reads a single element out of a buffer
let reader_t #a #p #q (#b:B.mbuffer a p q) (lens:buffer_hs_lens b) =
  i:uint_32{ i < B.len b } ->
  with_state lens a
    (requires fun _ -> True)
    (ensures fun s0 v s1 ->
      s0 == s1 /\
      v == Seq.index s1 (UInt32.v i))

/// `reader_t l`: writes a single element to a buffer
let writer_t #a #p #q (#b:B.mbuffer a p q) (lens:buffer_hs_lens b) =
  i:uint_32{ i < B.len b } ->
  v:a ->
  with_state lens unit
    (requires fun s0 -> 
      s0 `q` Seq.upd s0 (UInt32.v i) v)
    (ensures fun s0 _ s1 ->
      s1 `Seq.equal` Seq.upd s1 (UInt32.v i) v)

/// `buffer_lens`: A triple of a lens for a buffer and its
/// corresponding element readers and writers
noeq
type buffer_lens #a #p #q (b:B.mbuffer a p q) =
  | Mk : hs_lens:buffer_hs_lens b ->
         reader:reader_t hs_lens ->
         writer:writer_t hs_lens ->
         buffer_lens b

/// `lens_of`: Projecting out the `hs_lens` from a `buffer_lens`
let lens_of #a #p #q (#b:B.mbuffer a p q) (prw:buffer_lens b)
   : buffer_hs_lens b
   = prw.hs_lens

/// `mk`: Constructs a buffer_lens from a buffer and a given state
abstract
let mk #a #p #q (b:B.mbuffer a p q) (snap:HS.mem{B.live snap b})
  : Tot (l:buffer_lens b{(lens_of l).snapshot == snap})
  = let blens : buffer_hs_lens b =
        FStar.Classical.forall_intro_2 (B.g_upd_seq_as_seq b);
        let invariant (x:B.mbuffer a p q) (h:HS.mem) =
          B.live h x
        in
        let fp = Ghost.hide (B.loc_buffer b) in
        let get : get_t (imem (invariant b)) (lseq_of b) =
          fun h -> B.as_seq h b
        in
        let put : put_t (imem (invariant b)) (lseq_of b) =
          fun v h -> B.g_upd_seq b v h
        in
        let l : imem_lens (invariant b) (lseq_of b) fp = {
          get = get;
          put = put;
          lens_laws = ()
        }
        in
        {
          footprint = fp;
          invariant = invariant;
          x = b;
          snapshot = snap;
          l = l
        }
    in
    let reader : reader_t blens =
      fun i s ->
        reveal_inv();
        B.index b i
    in
    let writer : writer_t blens =
      fun i v s ->
        reveal_inv();
        B.upd b i v
    in
    Mk blens reader writer

/// `elim_inv`: Revealing the abstract invariant of buffer lenses
let elim_inv #a #p #q 
             (#b:B.mbuffer a p q)
             (bl:buffer_lens b)
             (h:HS.mem)
  : Lemma (let l = lens_of bl in
           (exists h'.{:pattern mk b h'} B.live h' b /\ bl == mk b h') /\
            inv l h ==>
             B.live h b /\
             view l h == B.as_seq h b)
  = reveal_inv ()

/// `index`: The analog of LowStar.Monotonic.Buffer.index
let index #a #p #q 
          (#b:B.mbuffer a p q)
          (bl:buffer_lens b)
          (i:uint_32{i < B.len b})
  : LensST a (lens_of bl)
    (requires fun _ -> True)
    (ensures fun s0 v s1 ->
      s0 == s1 /\
      v == Seq.index s1 (UInt32.v i))
  = reveal_inv ();
    let h = HST.get() in
    bl.reader i h

/// `upd`: The analog of LowStar.Monotonic.Buffer.upd
let upd #a #p #q 
          (#b:B.mbuffer a p q)
          (bl:buffer_lens b)
          (i:uint_32{i < B.len b})
          (v:a)
  : LensST unit (lens_of bl)
    (requires fun s0 ->
      s0 `q` Seq.upd s0 (UInt32.v i) v)
    (ensures fun s0 _ s1 ->
      s1 `Seq.equal` Seq.upd s1 (UInt32.v i) v)
  = reveal_inv ();
    let h = HST.get() in
    bl.writer i v h

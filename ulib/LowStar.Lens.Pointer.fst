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
module LowStar.Lens.Pointer
open LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.Integers

(* This module provides an instance of an `hs_lens` for monotonic
   pointers, allowing viewing a hyperstack containing a buffer as just
   the pointer's contents.
*)

let lift (p:Preorder.preorder 'a) : B.srel 'a =
  fun (s0 s1: Seq.seq 'a) ->
    Seq.length s0 == Seq.length s1 /\
    (Seq.length s0 == 1 ==>
     Seq.index s0 0 `p` Seq.index s1 0)

let lower (p:B.srel 'a) : Preorder.preorder 'a =
  fun v0 v1 ->
    Seq.create 1 v0 `p` Seq.create 1 v1
    
let ok (q:B.srel 'a) =
  forall (s0 s1 : Seq.seq 'a). {:pattern (s0 `q` s1)}
    (Seq.length s0 == Seq.length s1 /\
     Seq.length s0 == 1 /\
     (Seq.create 1 (Seq.index s0 0)) `q` (Seq.create 1 (Seq.index s1 0))) ==>
    s0 `q` s1

let ptr_rel 'a = q:B.srel 'a{ok q}
  
let pointer a p q =
  b:B.mbuffer a p q{B.length b == 1 /\ ok q}

/// `ptr_hs_lens`:
///   hs_lens between a ptr `b` and `lseq_of b`
let ptr_hs_lens #a #p #q (b:pointer a p q) =
  l:hs_lens (pointer a p q) a{
    Ghost.reveal l.footprint == B.loc_buffer b
  }

/// `reader_t l`: reads a single element out of a buffer
let reader_t #a #p #q (#b:pointer a p q) (lens:ptr_hs_lens b) =
  with_state lens a
    (requires fun _ -> True)
    (ensures fun s0 v s1 ->
      s0 == s1 /\
      v == s1)

/// `reader_t l`: writes a single element to a buffer
let writer_t #a #p #q (#b:pointer a p q) (lens:ptr_hs_lens b) =
  v:a ->
  with_state lens unit
    (requires fun s0 -> 
      s0 `lower q` v)
    (ensures fun s0 _ s1 ->
      s1 == v)

/// `buffer_lens`: A triple of a lens for a buffer and its
/// corresponding element readers and writers
noeq
type ptr_lens #a #p #q (b:pointer a p q) =
  | Mk : hs_lens:ptr_hs_lens b ->
         reader:reader_t hs_lens ->
         writer:writer_t hs_lens ->
         ptr_lens b

/// `lens_of`: Projecting out the `hs_lens` from a `buffer_lens`
let lens_of #a #p #q (#b:pointer a p q) (prw:ptr_lens b)
   : ptr_hs_lens b
   = prw.hs_lens

/// `mk`: Constructs a buffer_lens from a buffer and a given state
abstract
let mk #a #p #q (b:pointer a p q) (snap:HS.mem{B.live snap b})
  : Tot (l:ptr_lens b{(lens_of l).snapshot == snap})
  = let blens : ptr_hs_lens b =
        FStar.Classical.forall_intro_2 (B.g_upd_seq_as_seq b);
        let invariant (x:pointer a p q) (h:HS.mem) =
          B.live h x
        in
        let fp = Ghost.hide (B.loc_buffer b) in
        let get : get_t (imem (invariant b)) a =
          fun h -> B.get h b 0
        in
        let put : put_t (imem (invariant b)) a =
          fun v h -> B.g_upd b 0 v h
        in
        let l : imem_lens (invariant b) a fp = {
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
      fun s ->
        reveal_inv();
        B.index b 0ul
    in
    let writer : writer_t blens =
      fun v s ->
        reveal_inv();
        B.upd b 0ul v
    in
    Mk blens reader writer

/// `elim_inv`: Revealing the abstract invariant of buffer lenses
let elim_inv #a #p #q 
             (#b:pointer a p q)
             (bl:ptr_lens b)
             (h:HS.mem)
  : Lemma (let l = lens_of bl in
           (exists h'.{:pattern mk b h'} B.live h' b /\ bl == mk b h') /\
            inv l h ==>
             B.live h b /\
             view l h == B.get h b 0)
  = reveal_inv ()

/// `index`: The analog of LowStar.Monotonic.Buffer.index
let index #a #p #q 
          (#b:pointer a p q)
          (bl:ptr_lens b)
  : LensST a (lens_of bl)
    (requires fun _ -> True)
    (ensures fun s0 v s1 ->
      s0 == s1 /\
      v == s1)
  = reveal_inv ();
    let h = HST.get() in
    bl.reader h

/// `upd`: The analog of LowStar.Monotonic.Buffer.upd
let upd #a #p #q 
          (#b:pointer a p q)
          (bl:ptr_lens b)
          (v:a)
  : LensST unit (lens_of bl)
    (requires fun s0 ->
      Seq.create 1 s0 `q` Seq.create 1 v)
    (ensures fun s0 _ s1 ->
      s1 == v)
  = reveal_inv ();
    let h = HST.get() in
    bl.writer v h

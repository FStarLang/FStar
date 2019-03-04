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
   
   This is the main "leaf" instance of an `hs_lens`, since (almost)
   all mutable types in LowStar are expressed via monotonic buffers
   (referring to a sequence) or pointers (referring to a single
   element).

   This module multiplexes between the buffer and pointer views as "two
   flavors".

   Note, Low* also supports `ref` types, which are essentially
   equivalent to pointers. For uniformity, we recommend using `pointer`
   instead of `ref`.  *)

/// `flav`: Two varieties of references
type flav =
  | Buffer
  | Pointer

/// `ok_for_ptr q`: Pointers, unfortunately, are indexed by preorders on
/// sequences, rather than preorders on elements. So, we need some
/// conditions to ensure that a sequence preorder is appropriate for a
/// pointer.
let ok_for_ptr (q:B.srel 'a) =
  forall (s0 s1 : Seq.seq 'a). {:pattern (s0 `q` s1)}
    (Seq.length s0 == Seq.length s1 /\
     Seq.length s0 == 1 /\
     (Seq.create 1 (Seq.index s0 0)) `q` (Seq.create 1 (Seq.index s1 0))) ==>
    s0 `q` s1

/// `flavor`: A buffer `b` is described as Pointer-flavor if
///  -- its length is 1
///  -- its preorder is ok for pointers
let flavor #a #p #q (b:B.mbuffer a p q) =
  f:flav{ 
    f == Pointer ==>
    B.length b == 1 /\
    ok_for_ptr q
  }


/// A couple of convenient flavor abbreviations
unfold 
let ptr (b:B.pointer 'a) : flavor b = Pointer

unfold 
let buf (b:B.mbuffer 'a 'b 'c) : flavor b = Buffer


/// `lseq_of`: A sequence whose length matches the buffer's length
let lseq_of #a #p #q (b:B.mbuffer a p q) =
  Seq.lseq a (B.length b)

/// `view_type_of b f`: Provides an f-flavored voew on the buffer `b`
let view_type_of #a #p #q (b:B.mbuffer a p q) (f:flavor b) =
  match f with
  | Buffer -> lseq_of b
  | Pointer -> a

/// `buffer_hs_lens`:
///   hs_lens between a buffer `b` and `lseq_of b`
///   of flavor `f`
let buffer_hs_lens #a #p #q (b:B.mbuffer a p q) (f:flavor b) =
  l:hs_lens (B.mbuffer a p q) (view_type_of b f){
    Ghost.reveal l.footprint == B.loc_buffer b /\
    l.x == b
  }

/// `get_value_at` and `put_value_at`: provide a uniform sequence- or
///  element-based view on top of both flavors of buffers
unfold
let get_value_at #a #p #q (#b:B.mbuffer a p q) (#f:flavor b)
                 (v:view_type_of b f)
                 (i:uint_32{ i < B.len b })
    : a =
    match f with
    | Pointer -> v
    | Buffer -> Seq.index v (UInt32.v i)

unfold
let put_value_at #a #p #q (#b:B.mbuffer a p q) (#f:flavor b)
                 (v0:view_type_of b f)
                 (i:uint_32{ i < B.len b })
                 (x:a)
    : view_type_of b f =
    match f with
    | Pointer -> x
    | Buffer -> Seq.upd v0 (UInt32.v i) x

/// `as_seq` views both flavors as a sequence
unfold
let as_seq #a #p #q 
           (#b:B.mbuffer a p q)
           (#f:flavor b)
           (v0:view_type_of b f)
   : lseq_of b
   = match f with
     | Pointer -> Seq.create 1 v0
     | Buffer -> v0


/// `with_state t`:
///
///    A computation in `LensST` which supports updating the snapshot
///
///    This is a technical device, not intended for typical use in
///    client code, but is useful in libraries that provide support for
///    composing and de-composing hs_lenses.
let with_state #from #to
               (lens:hs_lens from to)
               ($t:hs_lens from to -> Type) =
  s:imem (lens.invariant lens.x) ->
  t (snap lens s)

let ix #a #p #q (b:B.mbuffer a p q) = i:uint_32{i < B.len b}

module LL = LowStar.Lens
/// `writer_t l`: writes a single element to a buffer
let reader_t #a #p #q (#b:B.mbuffer a p q) (f:flavor b)
             #from #to (layer: lens to (view_type_of b f))
             (l:hs_lens from to)
  = i:ix b ->
    LensST a l
      (requires fun _ -> True)
      (ensures fun s0 v s1 ->
        s0 == s1 /\
        v == get_value_at (LL.get layer s1) i)

/// `writer_t l`: writes a single element to a buffer
let writer_t #a #p #q (#b:B.mbuffer a p q) (f:flavor b)
             #from #to (layer: lens to (view_type_of b f))
             (l:hs_lens from to)
  = i:ix b ->
    v:a ->
    LensST unit l
      (requires fun s0 ->
        as_seq (LL.get layer s0) `q` as_seq (put_value_at (LL.get layer s0) i v))
      (ensures fun s0 _ s1 ->
        s1 == LL.put layer s0 (put_value_at (LL.get layer s0) i v))

unfold
let id_lens #a : lens a a = {
  get= (fun x -> x);
  put= (fun x s -> x);
  lens_laws = ()
}

/// `buffer_lens`: A triple of a lens for a buffer and its
/// corresponding element readers and writers
noeq
type buffer_lens #a #p #q (b:B.mbuffer a p q) (f:flavor b) =
  | Mk : hs_lens:buffer_hs_lens b f ->
         reader:with_state hs_lens (reader_t f id_lens) ->
         writer:with_state hs_lens (writer_t f id_lens)  ->
         buffer_lens b f

/// `lens_of`: Projecting out the `hs_lens` from a `buffer_lens`
let lens_of #a #p #q (#b:B.mbuffer a p q) (#f:flavor b) (prw:buffer_lens b f)
   : buffer_hs_lens b f
   = prw.hs_lens

/// `mk`: Constructs a buffer_lens from a buffer and a given state
abstract
let mk #a #p #q (b:B.mbuffer a p q) (f:flavor b) (snap:HS.mem{B.live snap b})
  : Tot (l:buffer_lens b f{(lens_of l).snapshot == snap})
  = let blens : buffer_hs_lens b f =
        FStar.Classical.forall_intro_2 (B.g_upd_seq_as_seq b);
        let invariant (x:B.mbuffer a p q) (h:HS.mem) =
          B.live h x
        in
        let fp = Ghost.hide (B.loc_buffer b) in
        let get : get_t (imem (invariant b)) (view_type_of b f) =
          fun h -> 
            match f with
            | Buffer -> B.as_seq h b
            | Pointer -> B.get h b 0
        in
        let put : put_t (imem (invariant b)) (view_type_of b f) =
          fun v h ->
            match f with
            | Buffer -> B.g_upd_seq b v h
            | Pointer -> B.g_upd b 0 v h
        in
        let l : imem_lens (invariant b) (view_type_of b f) fp = {
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
    let reader : with_state blens (reader_t f id_lens) =
      fun s i ->
        reveal_inv();
        B.index b i
    in
    let writer : with_state blens (writer_t f id_lens) =
      fun s i v ->
        reveal_inv();
        B.upd b i v
    in
    Mk blens reader writer

/// `elim_inv`: Revealing the abstract invariant of buffer lenses
let elim_inv #a #p #q 
             (#b:B.mbuffer a p q)
             (#f:flavor b)
             (bl:buffer_lens b f)
  : Lemma (reveal_inv();
          (forall (h:HS.mem).{:pattern (lens_of bl).invariant (lens_of bl).x h}
           let l = lens_of bl in
           (exists h'.{:pattern mk b f h'} B.live h' b /\ bl == mk b f h') /\
             (lens_of bl).invariant (lens_of bl).x h ==>
             B.live h b /\
             view (snap l h) h == 
               (match f with
                | Pointer -> B.get h b 0
                | Buffer -> B.as_seq h b)))
  = reveal_inv ()

/// `index`: The analog of LowStar.Monotonic.Buffer.index
let index #a #p #q 
          (#b:B.mbuffer a p q)
          (#f:flavor b)
          (bl:buffer_lens b f)
  : reader_t f id_lens (lens_of bl)
  = fun i -> 
    reveal_inv ();
    let h = HST.get() in
    bl.reader h i

/// `upd`: The analog of LowStar.Monotonic.Buffer.upd
let upd #a #p #q 
          (#b:B.mbuffer a p q)
          (#f:flavor b)
          (bl:buffer_lens b f)
  : writer_t f id_lens (lens_of bl)
  = fun i v -> 
    reveal_inv ();
    let h = HST.get() in
    bl.writer h i v

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
module LowStar.BufferView

(**
 * A "view" on a buffer allows treating a
 * `Buffer.buffer a` as a
 * `BufferView.buffer b`
 *
 * A "view" on a buffer is intended for specification purposes only
 * It does not correspond to a pointer cast in C.
 *
 * Building a view requires providing a pair of mutually inverse functions
 * from sequences of `a` (sub-sequences of the source buffer)
 * to elements of `b`.
 *
 **)
open LowStar.Monotonic.Buffer

module HS=FStar.HyperStack
module B=LowStar.Monotonic.Buffer

(** Definition of a view **)

/// `f` and `g` are mutual inverses
let inverses #a #b
             (f: (a -> GTot b))
             (g: (b -> GTot a)) =
  (forall x. g (f x) == x) /\
  (forall y. f (g y) == y)

/// `view a b` maps `n`-lengthed sequences of `a` to a single `b`
noeq
type view (a:Type) (b:Type) =
  | View : n:pos ->
           get:(Seq.lseq a n -> GTot b) ->
           put:(b -> GTot (Seq.lseq a n)) {
             inverses get put
           } ->
           view a b

/// `buffer_views src dest`:
///
/// The main abstract type provided by this module. This type is
/// indexed by both the `src` and `dest` types. The former (`src`) is
/// the type of the underlying B.buffer's contents: as such, it is
/// forced to be in universe 0.
///
/// The destination type `dest` is for specification only and is not
/// subject to the same universe constraints by the memory model.

val buffer_view (src:Type0) (rrel rel:B.srel src) (dest:Type u#b) : Type u#b

/// `buffer b`: In contrast to `buffer_view`, `buffer b` hides the
/// source type of the view. As such, it is likely more convenient to
/// use in specifications and the rest of this interface is designed
/// around this type.
///
/// However, the type has a higher universe, and
/// this means, for instance, that values of `buffer b` cannot be
/// stored in the heap.
///
/// We leave its definition transparent in case clients wish to
/// manipulate both the `src` and `dest` types explicitly (e.g., to
/// stay in a lower universe)

let buffer (dest:Type u#a) : Type u#(max a 1) = (src:Type0 & rrel:B.srel src & rel:B.srel src & buffer_view src rrel rel dest)

let as_buffer_t (#dest:Type) (b:buffer dest) = B.mbuffer (Mkdtuple4?._1 b) (Mkdtuple4?._2 b) (Mkdtuple4?._3 b)

/// `mk_buffer_view`: The main constructor
val mk_buffer_view (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
                   (b:B.mbuffer src rrel rel)
                   (v:view src dest{
                     length b % View?.n v == 0
                   })
   : GTot (buffer dest)


/// `as_buffer`: Projecting the underlying B.buffer from its view
val as_buffer (#b:Type) (v:buffer b) : as_buffer_t v

/// A lemma-relating projector to constructor
val as_buffer_mk_buffer_view (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
                             (b:B.mbuffer src rrel rel)
                             (v:view src dest{
                               length b % View?.n v == 0
                              })
    : Lemma (let bv = mk_buffer_view b v in
             Mkdtuple4?._1 bv == src  /\
	     Mkdtuple4?._2 bv == rrel /\
	     Mkdtuple4?._3 bv == rel  /\
             as_buffer bv == b)
            [SMTPat (as_buffer (mk_buffer_view b v))]

/// `get_view`: Projecting the view functions itself
val get_view  (#b : Type) (v:buffer b) : view (Mkdtuple4?._1 v) b

/// A lemma-relating projector to constructor
val get_view_mk_buffer_view (#src:Type0) (#rrel #rel:B.srel src) (#dest:Type)
                            (b:B.mbuffer src rrel rel)
                            (v:view src dest{
                               length b % View?.n v == 0
                             })
    : Lemma (let bv = mk_buffer_view b v in
             Mkdtuple4?._1 bv == src /\
             get_view bv == v)
            [SMTPat (get_view (mk_buffer_view b v))]

/// `live h vb`: liveness of a buffer view corresponds to liveness of
/// the underlying buffer
unfold
let live #b h (vb:buffer b) = live h (as_buffer vb)

/// `length vb`: is defined in terms of the underlying buffer
///
/// Internally, it is defined as
///
/// ```
/// length (as_buffer vb) / View?.n (get_view vb)
/// ```
///
/// However, rather than expose this definition (which uses non-linear
/// arithmetic) to callers, we treat length abstractly.
///
/// To reveal its definition explicitly, use the `length_eq` lemma below.
val length (#b: _) (vb:buffer b)
  : GTot nat

/// `length_eq`: Reveals the definition of the `length` function
val length_eq (#b: _) (vb:buffer b)
  : Lemma (length vb = B.length (as_buffer vb) / View?.n (get_view vb))

/// `view_indexing`: A lemma that requires a bit of non-linear
/// arithmetic, necessary for some of the specs below and convenient
/// when relating the underlying buffer to its view.
val view_indexing (#b: _) (vb:buffer b) (i:nat{i < length vb})
  : Lemma (let open FStar.Mul in
           let n = View?.n (get_view vb) in
           n <= length vb * n - i * n)

/// `sel h vb i` : selects element at index `i` from the buffer `vb` in heap `h`
val sel (#b: _)
        (h:HS.mem)
        (vb:buffer b)
        (i:nat{i < length vb})
   : GTot b

/// `upd h vb i x`: stores `x` at index `i` in the buffer `vb` in heap `h`
val upd (#b: _)
        (h:HS.mem)
        (vb:buffer b{live h vb})
        (i:nat{i < length vb})
        (x:b)
  : GTot HS.mem

/// `sel_upd`: A classic select/update lemma for reasoning about maps
val sel_upd (#b:_)
            (vb:buffer b)
            (i:nat{i < length vb})
            (j:nat{j < length vb})
            (x:b)
            (h:HS.mem{live h vb})
  : Lemma (if i = j
           then sel (upd h vb i x) vb j == x
           else sel (upd h vb i x) vb j == sel h vb j)
          [SMTPat (sel (upd h vb i x) vb j)]

val lemma_upd_with_sel (#b:_)
                       (vb:buffer b)
                       (i:nat{i < length vb})
                       (h:HS.mem{live h vb})
  :Lemma (upd h vb i (sel h vb i) == h)

/// `modifies` on views is just defined in terms of the underlying buffer
unfold
let modifies (#b: _)
             (vb:buffer b)
             (h h':HS.mem)
    = B.modifies (B.loc_buffer (as_buffer vb)) h h'

/// `upd_modifies`: Footprint of `upd`
val upd_modifies (#b: _)
                 (h:HS.mem)
                 (vb:buffer b{live h vb})
                 (i:nat{i < length vb})
                 (x:b)
    : Lemma (ensures (modifies vb h (upd h vb i x) /\
                      live (upd h vb i x) vb))
            [SMTPat (upd h vb i x)]

/// `upd_equal_domains`: `upd` does not modify the memory domains
val upd_equal_domains (#b: _)
                      (h:HS.mem)
                      (vb:buffer b{live h vb})
                      (i:nat{i < length vb})
                      (x:b)
    : Lemma (FStar.HyperStack.ST.equal_domains h (upd h vb i x))

/// `as_seq h vb`: Viewing the entire buffer as a sequence of `b`
val as_seq (#b: _) (h:HS.mem) (vb:buffer b)
   : GTot (Seq.lseq b (length vb))

/// `as_seq_sel`:
///
/// Relates selecting an element in the heap to selecting an element
/// from the sequence
val as_seq_sel (#b: _)
               (h:HS.mem)
               (vb:buffer b)
               (i:nat{i < length vb})
    : Lemma (sel h vb i == Seq.index (as_seq h vb) i)

/// `get_sel`:
///
/// Relates selecting an element from the view to translating a
/// subsequence of the underlying buffer through the view
val get_sel (#b: _)
            (h:HS.mem)
            (vb:buffer b)
            (i:nat{i < length vb})
    : Lemma (let open FStar.Mul in
             let v = get_view vb in
             let n = View?.n v in
             length_eq vb;
             view_indexing vb i;
             sel h vb i ==
             View?.get v (Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n)))

/// `put_sel`:
///
/// Relates selecting a subsequence of the underlying buffer
/// to selecting and translating an element from the view.
val put_sel (#b: _)
            (h:HS.mem)
            (vb:buffer b)
            (i:nat{i < length vb})
    : Lemma (let open FStar.Mul in
             let v = get_view vb in
             let n = View?.n v in
             length_eq vb;
             view_indexing vb i;
             View?.put v (sel h vb i) ==
             Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n))

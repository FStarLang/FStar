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
module LowStar.BufferView.Up

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
module Down=LowStar.BufferView.Down

(** Definition of a view **)

/// `f` and `g` are mutual inverses
let inverses = Down.inverses

/// `view a b` maps `n`-lengthed sequences of `a` to a single `b`
noeq
type view (a:Type) (b:Type) =
  | View : n:pos ->
           get:(Seq.lseq a n -> GTot b) ->
           put:(b -> GTot (Seq.lseq a n)) {
             inverses get put
           } ->
           view a b

val buffer (dest:Type0) : Type u#1

/// `mk_buffer`: The main constructor
val mk_buffer (#src:Type0)
              (#dest:Type0)
              (b:Down.buffer src)
              (v:view src dest{
                     Down.length b % View?.n v == 0
               })
   : GTot (buffer dest)

val buffer_src (#dest:Type) (b:buffer dest) : Type0

/// `as_down_buffer`: Projecting the underlying Down.buffer from its view
val as_down_buffer (#b:Type) (v:buffer b) : Down.buffer (buffer_src v)

/// `get_view`: Projecting the view functions itself
val get_view  (#b : Type) (v:buffer b) : view (buffer_src v) b

/// A lemma-relating projector to constructor
val as_buffer_mk_buffer (#src #dest:Type)
                        (d:Down.buffer src)
                        (v:view src dest{
                               Down.length d % View?.n v == 0
                         })
    : Lemma (let bv = mk_buffer d v in
             buffer_src bv == src /\
             as_down_buffer bv == d /\
             get_view bv == v)
            [SMTPatOr [[SMTPat (buffer_src (mk_buffer d v))];
                       [SMTPat (as_down_buffer (mk_buffer d v))];
                       [SMTPat (get_view (mk_buffer d v))]]]

/// `live h vb`: liveness of a buffer view corresponds to liveness of
/// the underlying buffer
unfold
let live #b h (vb:buffer b) = Down.live h (as_down_buffer vb)
val length (#b: _) (vb:buffer b)
  : GTot nat

/// `length_eq`: Reveals the definition of the `length` function
val length_eq (#b: _) (vb:buffer b)
  : Lemma (length vb = Down.length (as_down_buffer vb) / View?.n (get_view vb))

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
    = Down.modifies (as_down_buffer vb) h h'

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
             View?.get v (Seq.slice (Down.as_seq h (as_down_buffer vb)) (i * n) (i * n + n)))

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
             Seq.slice (Down.as_seq h (as_down_buffer vb)) (i * n) (i * n + n))

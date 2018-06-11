module LowStar.BufferView

(**
 * A "view" on a buffer allows treating a
 * `Buffer.buffer a` as a
 * `BufferView.buffer b`
 *
 * A "view" on a buffer is intended for specification purposes only
 * It does not correspond to a pointer cast in C.
 **)
open LowStar.Buffer
module HS=FStar.HyperStack
module B=LowStar.Buffer

let inverses #a #b
             (f: (a -> GTot b))
             (g: (b -> GTot a)) =
  (forall x. g (f x) == x) /\
  (forall y. f (g y) == y)

noeq
type view (a:Type) (b:Type) =
  | View : n:pos ->
           get:(Seq.lseq a n -> GTot b) ->
           put:(b -> GTot (Seq.lseq a n)) {
             inverses get put
           } ->
           view a b

val buffer_view (a:Type0) (b:Type) : Type0

let buffer (b:Type) : Type u#1 = (a:Type0 & buffer_view a b)

val mk_buffer_view (#src #dest:Type)
                   (b:B.buffer src)
                   (v:view src dest{
                     length b % View?.n v == 0
                   })
   : GTot (buffer_view src dest)

val as_buffer (#a #b : Type0) (v:buffer_view a b) : B.buffer a
val get_view  (#a #b : Type0) (v:buffer_view a b) : view a b

unfold
let live #a #b h (vb:buffer_view a b) =
    live h (as_buffer vb)

let length (#a #b: _) (vb:buffer_view a b)
  : GTot nat
  = length (as_buffer vb) / View?.n (get_view vb)

val view_indexing (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb})
  : Lemma (let open FStar.Mul in
           let n = View?.n (get_view vb) in
           n <= length vb * n - i * n)

val sel (#a #b: _)
        (vb:buffer_view a b)
        (i:nat{i < length vb})
        (h:HS.mem)
   : GTot b

val upd (#a #b: _)
        (vb:buffer_view a b)
        (i:nat{i < length vb})
        (x:b)
        (h:HS.mem{live h vb})
  : GTot HS.mem

val sel_upd (#a #b:_)
             (vb:buffer_view a b)
             (i:nat{i < length vb})
             (j:nat{j < length vb /\ i<>j})
             (x:b)
             (h:HS.mem{live h vb})
  : Lemma (if i = j
           then sel vb j (upd vb i x h) == x
           else sel vb j (upd vb i x h) == sel vb j h)
          [SMTPat (sel vb j (upd vb i x h))]

val as_seq (#a #b: _) (h:HS.mem) (vb:buffer_view a b)
   : GTot (Seq.lseq b (length vb))

val as_seq_sel (#a #b: _)
               (h:HS.mem)
               (vb:buffer_view a b)
               (i:nat{i < length vb})
    : Lemma (sel vb i h == Seq.index (as_seq h vb) i)

val get_sel (#a #b: _)
            (h:HS.mem)
            (vb:buffer_view a b)
            (i:nat{i < length vb})
    : Lemma (let open FStar.Mul in
             let v = get_view vb in
             let n = View?.n v in
             view_indexing vb i;
             sel vb i h ==
             View?.get v (Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n)))

val put_sel (#a #b: _)
            (h:HS.mem)
            (vb:buffer_view a b)
            (i:nat{i < length vb})
    : Lemma (let open FStar.Mul in
             let v = get_view vb in
             let n = View?.n v in
             view_indexing vb i;
             View?.put v (sel vb i h) ==
             Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n))

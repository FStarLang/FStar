module LowStar.BufferView
open LowStar.Buffer

let lseq a (n:nat) = s:Seq.seq a{Seq.length s = n}

let inverses #a #b (f: (a -> GTot b)) (g: (b -> GTot a)) =
  (forall x. g (f x) == x) /\ (forall y. f (g y) == y)

noeq
type view (a:Type) (b:Type) =
  | View : n:pos ->
           get:(lseq a n -> GTot b) ->
           put:(b -> GTot (lseq a n)) {
             inverses get put
           } ->
           view a b

noeq
type buffer_view (a:Type0) (b:Type0) : Type0 =
  | BufferView: buf:buffer a
              -> v:view a b{length buf % View?.n v == 0}
              -> buffer_view a b

val mk_buffer_view (#src #dest:Type)
                   (b:buffer src)
                   (v:view src dest{
                     length b % View?.n v == 0
                   })
   : GTot (buffer_view src dest)

let as_buffer (#a #b : Type0) (v:buffer_view a b) : buffer a =
    BufferView?.buf v

let get_view  (#a #b : Type0) (v:buffer_view a b) : view a b =
    BufferView?.v v

unfold
let live #a #b h (vb:buffer_view a b) =
    live h (as_buffer vb)

let length (#a #b: _) (vb:buffer_view a b)
  : GTot nat
  = length (as_buffer vb) / View?.n (get_view vb)

module HS=FStar.HyperStack

let as_seq (#a #b: _) (vb:buffer_view a b) (h:HS.mem{live h vb})
  : GTot (lseq b (length vb))
  = let s0 = as_seq h (as_buffer vb) in
    let v = get_view vb in
    let n = View?.n v in
    let rec get_seq
            (as:Seq.seq a{Seq.length as % n == 0})
          : GTot (bs:Seq.seq b{Seq.length bs = Seq.length as / n})
                (decreases (Seq.length as))
          = if Seq.length as = 0
            then Seq.createEmpty #b
            else let prefix, suffix = Seq.split as n in
                 assert (Seq.length suffix = Seq.length as - n);
                 FStar.Math.Lemmas.lemma_mod_sub (Seq.length as) n 1;
                 let tail = get_seq suffix in
                 Seq.cons (View?.get v prefix) tail
    in
    get_seq s0

let sel (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (h:HS.mem{live h vb})
   : GTot b
   = Seq.index (as_seq vb h) i

module B=LowStar.Buffer

let upd (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (x:b) (h:HS.mem{live h vb})
  : GTot HS.mem
  = let open FStar.Mul in
    let s0 = B.as_seq h (as_buffer vb) in
    let v = get_view vb in
    let n = View?.n v in
    let j = i * n in
    let prefix, suffix = Seq.split s0 j in
    assert (Seq.length suffix = Seq.length s0 - (i * n));
    assert (Seq.length s0 = length vb * n);
    assume (Seq.length suffix > n);
    let _, tail = Seq.split suffix n in
    let s1 = Seq.append prefix (Seq.append (View?.put v x) tail) in
    h

    g_upd (as_buffer vb) i (

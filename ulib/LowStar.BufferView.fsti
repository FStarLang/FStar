module LowStar.BufferView
open LowStar.Buffer

let inverses #a #b (f: (a -> GTot b)) (g: (b -> GTot a)) =
  (forall x. g (f x) == x) /\ (forall y. f (g y) == y)

noeq
type view (a:Type) (b:Type) =
  | View : n:pos ->
           get:(Seq.lseq a n -> GTot b) ->
           put:(b -> GTot (Seq.lseq a n)) {
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

let rec get_seq
        #a #b
        (v:view a b)
        (as:Seq.seq a{Seq.length as % View?.n v == 0})
      : GTot (bs:Seq.seq b{Seq.length bs = Seq.length as / View?.n v})
             (decreases (Seq.length as))
      = let n = View?.n v in
        if Seq.length as = 0
        then Seq.createEmpty #b
        else let prefix, suffix = Seq.split as n in
             assert (Seq.length suffix = Seq.length as - n);
             FStar.Math.Lemmas.lemma_mod_sub (Seq.length as) n 1;
             let tail = get_seq v suffix in
             Seq.cons (View?.get v prefix) tail

let as_seq (#a #b: _) (h:HS.mem) (vb:buffer_view a b)
  : GTot (Seq.lseq b (length vb))
  = let s0 = as_seq h (as_buffer vb) in
    let v = get_view vb in
    get_seq v s0

module B=LowStar.Buffer

#reset-options "--max_fuel 0 --max_ifuel 1"
let view_indexing (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb})
  : Lemma (let open FStar.Mul in
           let n = View?.n (get_view vb) in
           n <= length vb * n - i * n)
  = let n = View?.n (get_view vb) in
    FStar.Math.Lemmas.distributivity_add_left (length vb) (-i) n

let split_at_i (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (h:HS.mem)
    : GTot (frags:
               (Seq.seq a *
                Seq.lseq a (View?.n (get_view vb)) *
                Seq.seq a){
               let prefix, as, suffix = frags in
               B.as_seq h (as_buffer vb) ==
               (prefix `Seq.append` (as `Seq.append` suffix))
            }
    )
    = let open FStar.Mul in
      let s0 = B.as_seq h (as_buffer vb) in
      let v = get_view vb in
      let n = View?.n v in
      let start = i * n in
      view_indexing vb i;
      let prefix, suffix = Seq.split s0 start in
      Seq.lemma_split s0 start;
      let as, tail = Seq.split suffix n in
      Seq.lemma_split suffix n;
      prefix, as, tail

let sel (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (h:HS.mem)
   : GTot b
   = let v = get_view vb in
     let _, as, _ = split_at_i vb i h in
     View?.get v as

let upd (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (x:b) (h:HS.mem{live h vb})
  : GTot HS.mem
  = let open FStar.Mul in
    let v = get_view vb in
    let prefix, _, suffix = split_at_i vb i h in
    let s1 = prefix `Seq.append` (View?.put v x `Seq.append` suffix) in
    B.g_upd_seq (as_buffer vb) s1 h

//#reset-options "--z3rlimit_factor 2 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let sel_upd1 (#a #b:_) (vb:buffer_view a b) (i:nat{i < length vb}) (x:b) (h:HS.mem{live h vb})
  : Lemma (sel vb i (upd vb i x h) == x)
  = let v = get_view vb in
    view_indexing vb i;
    let h' = upd vb i x h in
    let prefix, as, suffix = split_at_i vb i h in
    let as' = View?.put v x in
    let s' = B.as_seq h' (as_buffer vb) in
    B.g_upd_seq_as_seq (as_buffer vb) (prefix `Seq.append` (as' `Seq.append` suffix)) h;
    assert (s' == prefix `Seq.append` (as' `Seq.append` suffix));
    let prefix', as'', suffix' = split_at_i vb i h' in
    assert (s' == prefix' `Seq.append` (as'' `Seq.append` suffix'));
    Seq.lemma_append_inj prefix  (as' `Seq.append` suffix)
                         prefix' (as'' `Seq.append` suffix');
    Seq.lemma_append_inj as' suffix
                         as'' suffix';
    assert (as' == as'')

#set-options "--z3rlimit_factor 3"
let sel_upd2 (#a #b:_) (vb:buffer_view a b) (i:nat{i < length vb}) (j:nat{j < length vb /\ i<>j}) (x:b) (h:HS.mem{live h vb})
  : Lemma (sel vb j (upd vb i x h) == sel vb j h)
  = let open FStar.Mul in
    let v = get_view vb in
    view_indexing vb i;
    view_indexing vb j;
    let h' = upd vb i x h in
    let s0 = B.as_seq h  (as_buffer vb) in
    let s1 = B.as_seq h' (as_buffer vb) in
    let min = if i < j then i else j in
    let max = if i < j then j else i in
    let n = View?.n v in
    assert (min < max);
    assume ((min * n) + n <= max * n);
    let p0, min0, m0, max0, t0 =
        Seq.slice s0 0 (min * n),
        Seq.slice s0 (min * n) ((min * n) + n),
        Seq.slice s0 ((min * n) + n) (max * n),
        Seq.slice s0 (max * n) ((max * n) + n),
        Seq.slice s0 ((max * n) + n) (length vb * n)
    in
    let p1, min1, m1, max1, t1 =
        Seq.slice s1 0 (min * n),
        Seq.slice s1 (min * n) ((min * n) + n),
        Seq.slice s1 ((min * n) + n) (max * n),
        Seq.slice s1 (max * n) ((max * n) + n),
        Seq.slice s1 ((max * n) + n) (length vb * n)
    in
    admit()



    let prefix, as, suffix = split_at_i vb i h in
    let as' = View?.put v x in
    let s' = B.as_seq h' (as_buffer vb) in
    B.g_upd_seq_as_seq (as_buffer vb) (prefix `Seq.append` (as' `Seq.append` suffix)) h;
    assert (s' == prefix `Seq.append` (as' `Seq.append` suffix));
    let prefix', as'', suffix' = split_at_i vb i h' in
    assert (s' == prefix' `Seq.append` (as'' `Seq.append` suffix'));
    Seq.lemma_append_inj prefix  (as' `Seq.append` suffix)
                         prefix' (as'' `Seq.append` suffix');
    Seq.lemma_append_inj as' suffix
                         as'' suffix';
    assert (prefix == prefix');
    assert (suffix == suffix');
    let prefix'', res, suffix'' = split_at_i vb j h' in

    ()


val sel_view (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (h:HS.mem)
   : Lemma (let open FStar.Mul in
            let as = B.as_seq h (as_buffer vb) in
            let v = get_view vb in
            let start = View?.n v * i in
            let finish = start + View?.n v in
            let a  = Seq.slice as start finish in
            sel vb i h == View?.get v a)
   = admit()Seq.index (as_seq h vb) i

let sel_vew #a #b (vb:buffer_view a b)


#set-options "--z3rlimit_factor 2"
let upd (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb}) (x:b) (h:HS.mem{live h vb})
  : GTot HS.mem
  = let open FStar.Mul in
    let s0 = B.as_seq h (as_buffer vb) in
    let v = get_view vb in
    let n = View?.n v in
    let j = i * n in
    let prefix, suffix = Seq.split s0 j in
    assert (Seq.length suffix = length vb * n - (i * n));
    FStar.Math.Lemmas.distributivity_add_left (length vb) (-i) n;
    let _, tail = Seq.split suffix n in
    let s1 = Seq.append prefix (Seq.append (View?.put v x) tail) in
    B.g_upd_seq (as_buffer vb) s1 h

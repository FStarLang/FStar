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
module B=LowStar.Buffer

#reset-options "--max_fuel 0 --max_ifuel 1"
let view_indexing (#a #b: _) (vb:buffer_view a b) (i:nat{i < length vb})
  : Lemma (let open FStar.Mul in
           let n = View?.n (get_view vb) in
           n <= length vb * n - i * n)
  = let n = View?.n (get_view vb) in
    FStar.Math.Lemmas.distributivity_add_left (length vb) (-i) n

let lt_leq_mul (min:nat) (max:nat{min < max}) (n:nat) :
  Lemma (FStar.Mul.(min * n + n <= max * n)) =
  let open FStar.Mul in
  assert ((min * n) + n = (min + 1) * n);
  assert ((min * n) + n <= max * n)

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


#reset-options "--max_fuel 0 --max_ifuel 1"
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
    lt_leq_mul min max n;
    let min0, max0 =
        Seq.slice s0 (min * n) ((min * n) + n),
        Seq.slice s0 (max * n) ((max * n) + n)
    in
    let _, s_j, _ = split_at_i vb j h in
    let min1, max1 =
        Seq.slice s1 (min * n) ((min * n) + n),
        Seq.slice s1 (max * n) ((max * n) + n)
    in
    let _, s_j', _ = split_at_i vb j h' in
    let prefix, s_i, suffix = split_at_i vb i h in
    B.g_upd_seq_as_seq (as_buffer vb) (prefix `Seq.append` (View?.put v x `Seq.append` suffix)) h;
    if i < j
    then begin
      assert (Seq.equal max0 s_j);
      assert (Seq.equal max1 s_j');
      assert (Seq.equal s_j s_j')
    end
    else begin
      assert (Seq.equal min0 s_j);
      assert (Seq.equal min1 s_j');
      assert (Seq.equal s_j s_j')
    end

let rec as_seq' (#a #b: _) (h:HS.mem) (vb:buffer_view a b) (i:nat{i <= length vb})
  : GTot (Seq.lseq b (length vb - i))
         (decreases (length vb - i))
  = let v = get_view vb in
    if i = length vb
    then Seq.createEmpty
    else let _ = view_indexing vb i in
         let _, s_i, suffix = split_at_i vb i h in
         View?.get v s_i `Seq.cons` as_seq' h vb (i + 1)

let as_seq (#a #b: _) (h:HS.mem) (vb:buffer_view a b) =
    as_seq' h vb 0

#set-options "--max_fuel 1 --max_ifuel 1"
let as_seq_sel (#a #b: _) (h:HS.mem) (vb:buffer_view a b) (i:nat{i < length vb})
    : Lemma (ensures (sel vb i h == Seq.index (as_seq h vb) i))
    =
      let rec as_seq'_as_seq' (#a #b: _)
                              (h:HS.mem)
                              (vb:buffer_view a b)
                              (j:nat)
                              (i:nat{j + i < length vb})
        : Lemma (ensures (Seq.index (as_seq' h vb j) i == Seq.index (as_seq' h vb (j + i)) 0))
                (decreases i)
        = if i = 0 then () else as_seq'_as_seq' h vb (j + 1) (i - 1)
      in
      as_seq'_as_seq' h vb 0 i

#set-options "--max_fuel 0 --max_ifuel 1"
let get_sel (#a #b: _) (h:HS.mem) (vb:buffer_view a b) (i:nat{i < length vb})
    : Lemma (ensures (let open FStar.Mul in
                      let v = get_view vb in
                      let n = View?.n v in
                      view_indexing vb i;
                      sel vb i h ==
                      View?.get v (Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n))))
    = ()

let put_sel (#a #b: _) (h:HS.mem) (vb:buffer_view a b) (i:nat{i < length vb})
    : Lemma (ensures (let open FStar.Mul in
                      let v = get_view vb in
                      let n = View?.n v in
                      view_indexing vb i;
                      View?.put v (sel vb i h) ==
                      Seq.slice (B.as_seq h (as_buffer vb)) (i * n) (i * n + n)))
    = get_sel h vb i

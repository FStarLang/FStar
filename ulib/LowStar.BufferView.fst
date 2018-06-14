module LowStar.BufferView

noeq
type buffer_view (a:Type0) (b:Type u#b) : Type0 =
  | BufferView: buf:buffer a
              -> v:view a b{length buf % View?.n v == 0}
              -> buffer_view a b

let mk_buffer_view #src #dest b v  = (| src, BufferView b v |)

let as_buffer (#b : Type) (v:buffer b) =
    BufferView?.buf (dsnd v)

let as_buffer_mk_buffer_view (#src #dest:Type)
                             (b:B.buffer src)
                             (v:view src dest{
                               length b % View?.n v == 0
                              }) = ()

let get_view  (#b : Type) (v:buffer b) =
    BufferView?.v (dsnd v)

let get_view_mk_buffer_view (#src #dest:Type)
                            (b:B.buffer src)
                            (v:view src dest{
                               length b % View?.n v == 0
                             }) = ()

let length (#b: _) (vb:buffer b)
  : GTot nat
  = B.length (as_buffer vb) / View?.n (get_view vb)

let length_eq (#b: _) (vb:buffer b) = ()

#reset-options "--max_fuel 0 --max_ifuel 1"
let view_indexing (#b: _) (vb:buffer b) (i:nat{i < length vb})
  = let n = View?.n (get_view vb) in
    FStar.Math.Lemmas.distributivity_add_left (length vb) (-i) n

let lt_leq_mul (min:nat) (max:nat{min < max}) (n:nat)
   : Lemma (FStar.Mul.(min * n + n <= max * n))
   = let open FStar.Mul in
     assert ((min * n) + n = (min + 1) * n);
     assert ((min * n) + n <= max * n)

let split_at_i (#b: _) (vb:buffer b) (i:nat{i < length vb}) (h:HS.mem)
    : GTot (frags:
               (Seq.seq (dfst vb) *
                Seq.lseq (dfst vb) (View?.n (get_view vb)) *
                Seq.seq (dfst vb)){
               let prefix, as, suffix = frags in
               B.as_seq h (as_buffer vb) ==
               (prefix `Seq.append` (as `Seq.append` suffix))
            })
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

let sel (#b: _) (h:HS.mem) (vb:buffer b) (i:nat{i < length vb})
   : GTot b
   = let v = get_view vb in
     let _, as, _ = split_at_i vb i h in
     View?.get v as

let upd (#b: _) (h:HS.mem) (vb:buffer b{live h vb}) (i:nat{i < length vb}) (x:b)
  : GTot HS.mem
  = let open FStar.Mul in
    let v = get_view vb in
    let prefix, _, suffix = split_at_i vb i h in
    let s1 = prefix `Seq.append` (View?.put v x `Seq.append` suffix) in
    B.g_upd_seq (as_buffer vb) s1 h

let sel_upd1 (#b:_) (vb:buffer b) (i:nat{i < length vb}) (x:b) (h:HS.mem{live h vb})
   : Lemma (sel (upd h vb i x) vb i == x)
   =
    let v = get_view vb in
    view_indexing vb i;
    let h' = upd h vb i x in
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

#set-options "--z3rlimit_factor 2"
let sel_upd2 (#b:_) (vb:buffer b)
             (i:nat{i < length vb})
             (j:nat{j < length vb /\ i<>j})
             (x:b)
             (h:HS.mem{live h vb})
  : Lemma (sel (upd h vb i x) vb j == sel h vb j)
  = let open FStar.Mul in
    let v = get_view vb in
    view_indexing vb i;
    view_indexing vb j;
    let h' = upd h vb i x in
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

let sel_upd (#b:_)
            (vb:buffer b)
            (i:nat{i < length vb})
            (j:nat{j < length vb})
            (x:b)
            (h:HS.mem{live h vb}) =
    if i=j then sel_upd1 vb i x h
    else sel_upd2 vb i j x h

let upd_modifies #b h vb i x
  = let open FStar.Mul in
    let v = get_view vb in
    let prefix, _, suffix = split_at_i vb i h in
    let s1 = prefix `Seq.append` (View?.put v x `Seq.append` suffix) in
    B.g_upd_seq_as_seq (as_buffer vb) s1 h

let rec as_seq' (#b: _) (h:HS.mem) (vb:buffer b) (i:nat{i <= length vb})
  : GTot (Seq.lseq b (length vb - i))
         (decreases (length vb - i))
  = let v = get_view vb in
    if i = length vb
    then Seq.createEmpty
    else let _ = view_indexing vb i in
         let _, s_i, suffix = split_at_i vb i h in
         View?.get v s_i `Seq.cons` as_seq' h vb (i + 1)

let as_seq (#b: _) (h:HS.mem) (vb:buffer b) = as_seq' h vb 0

#set-options "--max_fuel 1 --max_ifuel 1"
let as_seq_sel (#b: _) (h:HS.mem) (vb:buffer b) (i:nat{i < length vb})
    : Lemma (ensures (sel h vb i == Seq.index (as_seq h vb) i))
    =
      let rec as_seq'_as_seq' (j:nat)
                              (i:nat{j + i < length vb})
        : Lemma (ensures (Seq.index (as_seq' h vb j) i == Seq.index (as_seq' h vb (j + i)) 0))
                (decreases i)
        = if i = 0 then () else as_seq'_as_seq' (j + 1) (i - 1)
      in
      as_seq'_as_seq' 0 i

#set-options "--max_fuel 0 --max_ifuel 1"
let get_sel (#b: _) (h:HS.mem) (vb:buffer b) (i:nat{i < length vb}) = ()
let put_sel (#b: _) (h:HS.mem) (vb:buffer b) (i:nat{i < length vb}) = ()

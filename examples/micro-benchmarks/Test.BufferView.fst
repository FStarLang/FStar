module Test.BufferView
open FStar.HyperStack
open FStar.HyperStack.ST
module L = LowStar.BufferView
module B = LowStar.Buffer

let v : L.view int (int * int) =
  let get (s:Seq.lseq int 2) : int * int = Seq.index s 0, Seq.index s 1 in
  let put (x, y) : Seq.lseq int 2 = Seq.upd (Seq.create 2 x) 1 y in
  assert (forall x. put (get x) `Seq.equal` x);
  L.View 2 get put

let bsel #a h (x:B.buffer a) (i:nat{i<B.length x}) = Seq.index (B.as_seq h x) i

let use_view (n:pos) (i:nat{i<n}) (vb:L.buffer (int * int) {L.length vb = n}) (h:mem)
  : Ghost mem
    (requires L.live h vb)
    (ensures (fun h' ->
                L.live h' vb /\
                L.modifies vb h h' /\
                L.sel h' vb i = (17, 42)))
  = let h' = L.upd h vb i (17, 42) in
    L.get_sel h' vb i;
    h'

let test (n:pos) (i:nat {i < n}) (b:B.buffer int {B.length b = FStar.Mul.(2 * n)}) (h:mem)
  : Ghost mem
          (requires B.live h b)
          (ensures (fun h' ->
                      let open FStar.Mul in
                      B.live h' b /\
                      B.modifies_1 b h h' /\
                      bsel h' b (i * 2) == 17 /\
                      bsel h' b (i * 2 + 1) == 42))
  = let open FStar.Mul in
    let m = 2 * n in
    let vb  = L.mk_buffer_view b v in
    L.as_buffer_mk_buffer_view b v;
    L.get_view_mk_buffer_view b v;
    L.length_eq vb;
    assert (L.length vb = n);
    let x, y = L.sel h vb i in
    L.view_indexing vb i;
    L.get_sel h vb i;
    assert (x == bsel h b (i * 2));
    assert (y == bsel h b ((i * 2) + 1));
    let h' = use_view n i vb h in
    L.get_sel h' vb i;
    h'

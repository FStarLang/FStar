module FreezeArray

open FStar.Preorder
open FStar.Heap
open FStar.ST

module Seq = FStar.Seq
module Set = FStar.Set

private type repr (a:Type0) (n:nat) :Type0 =
  t:(Seq.seq (option a) * bool){Seq.length (fst t) = n /\ (b2t (snd t) ==> (forall (i:nat). i < n ==> Some? (Seq.index (fst t) i)))}

(*
 * the array is initialize once array
 * before it is frozen, it's wild west
 * once it's frozen, all elements have been initialized and the array does not change after that
 *)
private type seq_rel (a:Type0) (n:nat) :relation (repr a n)
  = fun (t1:repr a n) (t2:repr a n) -> let s1, b1 = t1 in
                                    let s2, b2 = t2 in
				    (b2t b1 ==> (b2t b2 /\ (s1 == s2)))

private let seq_pre (a:Type0) (n:nat) :preorder (repr a n) = seq_rel a n

noeq abstract type array (a:Type0) (n:nat) =
  | A: #m:nat -> s_ref:mref (repr a m) (seq_pre a m)
       -> offset:nat{offset + n <= m} -> array a n

abstract let is_full_array (#a:Type0) (#n:nat) (arr:array a n) :bool =
  let A #_ #_ #m _ off = arr in
  off = 0 && n = m

abstract let array_footprint (#a:Type0) (#n:nat) (arr:array a n) :GTot (Set.set nat)
  = let A s_ref _ = arr in
    Set.singleton (addr_of s_ref)

abstract let contains_array (#a:Type) (#n:nat) (h:heap) (arr:array a n)
  = let A #_ s_ref _ = arr in
    h `contains` s_ref

abstract let initializable (#a:Type0) (#n:nat) (arr:array a n) (h:heap)
  = let A #_ s_ref _ = arr in
    not (snd (sel h s_ref))

let fresh_arr (#a:Type0) (#n:nat) (arr:array a n) (h0 h1:heap)
  = h1 `contains_array` arr /\
    initializable arr h1    /\
    (forall (n:nat). Set.mem n (array_footprint arr) ==> n `addr_unused_in` h0)
    
abstract let create (a:Type0) (n:nat)
  :ST (array a n) (requires (fun _         -> True))
                  (ensures  (fun h0 arr h1 -> fresh_arr arr h0 h1      /\
		                           modifies Set.empty h0 h1 /\
					   initializable arr h1     /\
					   is_full_array arr))
  = A #a #n #n (alloc ((Seq.create n None), false)) 0

type index (#a:Type0) (#n:nat) (arr:array a n) = i:nat{i < n}

abstract let as_seq (#a:Type0) (#n:nat) (arr:array a n) (h:heap) :GTot (s:Seq.seq (option a){Seq.length s = n})
  = let A #_ #_ #_ s_ref off = arr in
    let s = fst (sel h s_ref) in
    Seq.slice s off (off + n)

let equivalent_seqs (#a:Type0) (s1:Seq.seq (option a)) (s2:Seq.seq a) :Type0
  = (Seq.length s1 == Seq.length s2) /\
    (forall (i:nat). i < Seq.length s1 ==> Some (Seq.index s2 i) == Seq.index s1 i)

let init_at_seq (#a:Type0) (s:Seq.seq (option a)) (i:nat{i < Seq.length s}) :Type0
  = Some? (Seq.index s i)

abstract let init_at (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i < n}) (h:heap) :Type0
  = let s = as_seq arr h in
    init_at_seq s i

assume val get_equivalent_seq (#a:Type0) (s:Seq.seq (option a){forall (i:nat). i < Seq.length s ==> Some? (Seq.index s i)})
  :Tot (r:Seq.seq a{equivalent_seqs s r})

private let frozen_bit (#a:Type0) (#n:nat) (arr:array a n) (h:heap) :GTot bool
  = let A #_ s_ref _ = arr in
    snd (sel h s_ref)

private type frozen_pred' (#a:Type0) (#n:nat) (arr:array a n) (s:Seq.seq a) :heap_predicate
  = fun h -> h `contains_array` arr /\ equivalent_seqs (as_seq arr h) s /\ frozen_bit arr h

open FStar.Ghost

abstract type frozen_pred (#a:Type0) (#n:nat) (arr:array a n) (s:erased (Seq.seq a)) :(p:heap_predicate{stable p})
  = frozen_pred' arr (reveal s)

abstract type frozen_with (#a:Type0) (#n:nat) (arr:array a n) (s:erased (Seq.seq a)) :Type0
  = Seq.length (reveal s) == n /\ witnessed (frozen_pred arr s)

abstract let freeze (#a:Type0) (#n:nat) (arr:array a n)
  :ST (s:erased (Seq.seq a))
      (requires (fun h0       -> is_full_array arr /\ (forall (i:nat). i < n ==> init_at arr i h0)))
      (ensures  (fun h0 es h1 -> equivalent_seqs (as_seq arr h0) (reveal es) /\
                              frozen_with arr es /\ modifies (array_footprint arr) h0 h1))
  = let A #_ s_ref _ = arr in
    let s, b = !s_ref in
    s_ref := (s, true);
    gst_witness (frozen_pred arr (hide (get_equivalent_seq s)));
    hide (get_equivalent_seq s)

abstract let read (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i < n}) (es:erased (Seq.seq a){frozen_with arr es})
  :ST a (requires (fun h0      -> True))
        (ensures  (fun h0 r h1 -> h0 == h1 /\ Seq.index (reveal es) i == r))
  = gst_recall (frozen_pred arr es);
    let A #_ s_ref o = arr in
    let (s, _) = !s_ref in
    Some?.v (Seq.index s (o + i))

abstract let write (#a:Type0) (#n:nat) (arr:array a n) (i:nat{i < n}) (x:a)
  :ST unit (requires (fun h0       -> initializable arr h0))
           (ensures  (fun h0 () h1 -> modifies (array_footprint arr) h0 h1 /\
	                           initializable arr h1                 /\
				   Seq.index (as_seq arr h1) i == Some x))
  = let A #_ s_ref offset = arr in
    let (s, b) = !s_ref in
    let s = Seq.upd s (offset + i) (Some x) in
    s_ref := (s, b);
    ()
	                           
abstract let sub (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) (len:nat{i + len <= n}) :array a len
  = let A #m s_ref o = arr in
    A #m s_ref (o + i)

let suffix (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) = sub arr i (n - i)
let prefix (#a:Type0) (#n:nat) (arr:array a n) (i:index arr) = sub arr 0 i

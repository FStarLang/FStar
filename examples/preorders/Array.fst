module Array

open FStar.Heap
open FStar.ST
module Set = FStar.Set
module Seq = FStar.Seq
module P = FStar.Preorder

type t (a:Type) (n:nat) = s:Seq.seq (option a){Seq.length s == n}
let remains_init0 (#a:Type) (#n:nat) : P.relation (t a n) = fun (s1 s2 : t a n) ->
    forall (i:nat{i < n}). Some? (Seq.index s1 i) ==> Some? (Seq.index s2 i)

let remains_init_preorder (#a:Type) (#n:nat) : Lemma (P.preorder_rel (rel0 #a #n)) = ()
let remains_init (#a:Type) (#n:nat) : P.preorder (t a n) = remains_init_preorder #a #n ; rel0

noeq
type array0 (n:nat) (a:Type) : Type =
  | Array: #m:nat -> r:mref (t a m) remains_init -> offset:nat{offset + n <= m} -> array0 n a

let array = array0

let fresh (#a:Type) (#n:nat) (x:array n a) (h0 h1:heap) = fresh (Array?.r x) h0 h1
let addr_of #a #n (Array r _) = addr_of r

let create a n = Array #n #_ #n (alloc (Seq.create n None)) 0
let sub #a #n (Array r o) i len = Array r (o + i)
let op_String_Access #a #n h0 (Array r o) = Seq.slice (sel h0 r) o (o+n)
let initialized0 #a #n (x:array n a) (i:nat{i < n}) h =
  h `contains` (Array?.r x) /\ Some? (Seq.index (sel h (Array?.r x)) (Array?.offset x + i))
let initialized0_stable #a #n (x:array n a) (i:nat{i < n}) : Lemma (stable (initialized0 x i)) =
    let Array #_ #_ #m r o = x in
    let i0 : k:nat{k < m} = o + i in
    assert (forall (h1 h2:heap). initialized0 x i h1 /\ heap_rel h1 h2 ==> rel0 (sel h1 r) (sel h2 r)) ;
    assert (forall (h1 h2:heap). initialized0 x i h1 /\ heap_rel h1 h2 ==>
                (Some? (Seq.index (sel h1 r) i0) ==> Some? (Seq.index (sel h2 r) i0))
    ) ;
    assert (forall (h1 h2:heap). initialized0 x i h1 /\ heap_rel h1 h2 ==> Some? (Seq.index (sel h2 r) i0))

let initialized #a #n (x:array n a) (i:nat{i < n}) : p:heap_predicate{stable p} =
  initialized0_stable x i ; initialized0 x i

let init_at #a #n x i = witnessed (initialized x i)
let all_init (#n:nat) (#a:Type) (x:array n a) = forall (i:index x). x `init_at` i
let iarray n a = x:array n a {all_init x}
let write #a #n (Array r o) i v =
  let s = !r in
  r := Seq.upd s (o + i) (Some v) ;
  gst_witness (initialized #_ #n (Array r o) i)
let read #a #n (Array r o) i = gst_recall (initialized #_ #n (Array r o) i); let s = !r in Some?.v (Seq.index s (o + i))

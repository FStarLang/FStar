(* Mutable arrays *)
module Array
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open Seq
open ST
open Heap
(* private *) type array (t:Type) = ref (seq t)



assume val of_seq: a:Type -> s:seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x) 
                             /\ contains h1 x 
                             /\ sel h1 x=s)))
  (modifies no_refs)

assume val to_seq: a:Type -> s:array a -> ST (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> (sel h0 s=x)))
  (modifies no_refs)

assume val create : a:Type -> n:nat -> init:a -> ST (array a) 
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> (not(contains h0 x) 
                             /\ contains h1 x 
                             /\ sel h1 x=Seq.create n init)))
  (modifies no_refs)

assume val index : a:Type -> x:array a -> n:nat -> ST a
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 v h1 -> (n < Seq.length (sel h0 x)
                             /\ v=Seq.index (sel h0 x) n)))
  (modifies no_refs)


assume val upd : a:Type -> x:array a -> n:nat -> v:a -> ST unit
  (requires (fun h -> contains h x /\ n < Seq.length (sel h x)))
  (ensures  (fun h0 u h1 -> (n < Seq.length (sel h0 x)
                            /\ sel h1 x=Seq.upd (sel h0 x) n v)))
  (modifies (a_ref x))

assume val length: a:Type -> x:array a -> ST nat
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> y=length (sel h0 x)))
  (modifies no_refs)

assume val op: a:Type -> f:(seq a -> Tot (seq a)) -> x:array a -> ST unit
  (requires (fun h -> contains h x))
  (ensures  (fun h0 u h1 -> sel h1 x=f (sel h0 x)))
  (modifies (a_ref x))


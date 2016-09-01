module NatHeap

open FStar.Classical
open FStar.Set
open Preorder

(* Heap is a tuple of a source of freshness (the no. of the next 
   reference to be allocated) and a mapping of allocated raw 
   references (represented as natural numbers) to types and values. *)

abstract noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & a))
}  

abstract type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> is_None (h.memory n))}

(* Consistency of heaps. aka, no strong updates *)
let consistent (h0:heap) (h1:heap) =
  forall n x y. h0.memory n == Some x /\ h1.memory n == Some y ==> dfst x == dfst y

(* References. *)
(* address * initial value *)
(* TODO: test that hasEq for ref is not exported *)
abstract type ref (a:Type0) = {
  addr: nat;
  init: a
}  

abstract val addr_of: #a:Type -> ref a -> Tot nat
let addr_of #a r = r.addr

abstract let contains (#a:Type) (h:heap) (r:ref a) =
  exists x. h.memory r.addr == Some (| a, x |)

(* Select. *)
private abstract val sel_tot : #a:Type -> h:heap -> r:ref a{contains h r} -> Tot a
let sel_tot #a h r =
  match h.memory r.addr with
  | Some (| _ , x |) -> x

abstract val sel: #a:Type -> h:heap -> r:ref a -> GTot a
let sel #a h r =
  if FStar.Classical.excluded_middle (contains h r) then
    sel_tot #a h r
  else r.init

(* Update. *)
private abstract val upd_tot : #a:Type -> h0:heap -> r:ref a{contains h0 r} -> x:a
          -> Tot (h1:heap{contains h1 r /\
	                 sel_tot h1 r == x /\
		         (forall b (r':ref b).{:pattern (contains h0 r')}
		       	    contains h0 r' ==> contains h1 r') /\
		         (forall b (r':ref b{contains h0 r'}).{:pattern sel_tot h0 r'}
		            r.addr <> r'.addr ==> sel_tot h0 r' == sel_tot h1 r')})
let upd_tot #a h0 r x =
  { h0 with memory = (fun r' -> if r.addr = r'
			     then Some (| a , x |)
                             else h0.memory r') }

abstract val upd: #a:Type -> h0:heap -> r:ref a -> x:a
 -> GTot (h1:heap{contains h1 r /\
	               sel_tot h1 r == x /\
		       (forall b (r':ref b) . {:pattern (contains h0 r')}
		       	  r'.addr <> r.addr /\ contains h0 r'
		       	  ==>
		       	  contains h1 r') /\
		       (forall b (r':ref b{contains h0 r'}) . {:pattern sel_tot h0 r'}
		          r.addr <> r'.addr ==>
		       	  sel_tot h0 r' == sel_tot h1 r')})
let upd #a h0 r x =
  if FStar.Classical.excluded_middle (contains h0 r)
  then upd_tot h0 r x
  else
    if r.addr >= h0.next_addr
    then //alloc at r.addr
      { next_addr = r.addr + 1;
        memory    = (fun (r':nat) -> if r' = r.addr
			        then Some (| a, x |)
                                else h0.memory r') }
    else //type modifying update at r.addr
      { h0 with memory = (fun r' -> if r' = r.addr
				 then Some (| a , x |)
                                 else h0.memory r') }

(* Generating a fresh reference for the given heap. *)

abstract val alloc: #a:Type -> h0:heap -> x:a -> GTot (rh1:(ref a * heap))
			 (* {~(contains h0 (fst rh1)) /\  *)
			 (*  contains (snd rh1) (fst rh1) /\ *)
		         (*  sel (snd rh1) (fst rh1) == x /\ *)
			 (*  (forall b (r:ref b) .{:pattern (contains h0 r)} *)
			 (*     contains h0 r  *)
			 (*     ==>  *)
			 (*     contains (snd rh1) r) /\ *)
			 (*  (forall b (r:ref b{contains h0 r}) . {:pattern sel #b h0 r} *)
			 (*     sel #b h0 r == sel #b (snd rh1) r)}) *)
let alloc #a h0 x =
  let r = { addr = h0.next_addr; init = x } in
  r, upd #a h0 r x

abstract let in_heap (#a:Type) (r:ref a)(h:heap) :GTot Type0 =
  is_Some (h.memory r.addr)

val contains_implies_in_heap: #a:Type -> h:heap -> r:ref a
                              -> Lemma (requires (h `contains` r))
			              (ensures (r `in_heap` h))
				[SMTPatOr [[SMTPat (h `contains` r)]; [SMTPat (r `in_heap` h)]]]
let contains_implies_in_heap #a h r = ()

val in_heap_addr_of: #a:Type -> #b:Type -> h:heap -> r1:ref a -> r2:ref b
                     -> Lemma (requires (r1 `in_heap` h /\ ~ (r2 `in_heap` h)))
		             (ensures (addr_of r1 <> addr_of r2))
		       [SMTPat (r1 `in_heap` h); SMTPat (r2 `in_heap` h)]
let in_heap_addr_of #a #b h r1 r2 = ()

let fresh (s:set nat) (h0:heap) (h1:heap) =
  forall (a:Type) (r:ref a).{:pattern (h0 `contains` r)}
                       mem (addr_of r) s ==> ~ (r `in_heap` h0) /\ (r `in_heap` h1)

let only x = singleton (addr_of x)

val alloc_lemma: #a:Type -> h0:heap -> x:a
                 -> Lemma (requires (True))
		         (ensures (let r, h1 = alloc h0 x in
			           h1 == upd h0 r x /\ ~ (h0 `contains` r) /\ h1 `contains` r))
		   [SMTPat (alloc h0 x)]
let alloc_lemma #a h0 x = ()

val sel_upd1: #a:Type -> h:heap -> r:ref a -> v:a
	      -> Lemma (requires True) (ensures (sel (upd h r v) r == v))
                [SMTPat (sel (upd h r v) r)]
let sel_upd1 #a h r v = ()

val sel_upd2: #a:Type -> #b:Type -> h:heap -> k1:ref a -> k2:ref b -> v:b
              -> Lemma (requires True) (ensures (addr_of k1 <> addr_of k2 ==> sel (upd h k2 v) k1 == sel h k1))
	        [SMTPat (sel (upd h k2 v) k1)]
let sel_upd2 #a #b h k1 k2 v = ()	     

val upd_sel : #a:Type -> h:heap -> r:ref a -> 
	      Lemma (requires (h `contains` r))
	            (ensures  (upd h r (sel h r) == h))
	      [SMTPat (upd h r (sel h r))]
let upd_sel #a h r = 
  assert (FStar.FunctionalExtensionality.feq (upd h r (sel h r)).memory h.memory)

(* Empty. *)
val emp : heap
let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

val in_dom_emp: #a:Type -> k:ref a
                -> Lemma (requires True) (ensures (~ (contains emp k)))
		  [SMTPat (contains emp k)]
let in_dom_emp #a k = ()

val upd_contains: #a:Type -> h:heap -> r:ref a -> v:a
                  -> Lemma (requires True) (ensures (contains (upd h r v) r))
		    [SMTPat (contains (upd h r v) r)]
let upd_contains #a h r v = ()



let modifies (s:set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ~ (mem (addr_of r) s) /\ h0 `contains` r ==>
                         sel h1 r == sel h0 r) /\
  (forall (a:Type) (r:ref a).{:pattern (h1 `contains` r)}
                        h0 `contains` r ==> h1 `contains` r)

abstract val lemma_modifies_trans: m1:heap -> m2:heap -> m3:heap
                       -> s1:set nat -> s2:set nat
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

val op_Hat_Plus_Plus: #a:Type -> r:ref a -> set nat -> Tot (set nat)
let op_Hat_Plus_Plus #a r s = union (only r) s

val op_Plus_Plus_Hat: #a:Type -> set nat -> r:ref a -> Tot (set nat)
let op_Plus_Plus_Hat #a s r = union s (only r)

val op_Hat_Plus_Hat: #a:Type -> #b:Type -> ref a -> ref b -> Tot (set nat)
let op_Hat_Plus_Hat #a #b r1 r2 = union (only r1) (only r2)

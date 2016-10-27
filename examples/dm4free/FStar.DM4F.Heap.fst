(* A model of a total heap which may only store values in Type0. 
   E.g., the heap may store zero-order values
      or higher order functions, so long as these functions do not manipulate the heap
*)
module FStar.DM4F.Heap
open FStar.Set

(* pre_heap: Type 1 *)
abstract noeq type pre_heap = {
  next_addr: nat; //the address of the next reference to be allocated
  memory   : nat -> Tot (option (a:Type0 & a)) //a map from addresses to allocated values (at some type)
}  

(* A heap is a pre_heap together with an invariant that nothing is allocated beyond next_addr *)
abstract type heap = h:pre_heap{forall (n:nat). n >= h.next_addr ==> is_None (h.memory n)}

(* References are represented by just their address in the heap *)
type ref (a:Type) = nat
let addr (#a:Type) (r:ref a) : Tot nat = r

(* An abstract predicate for a reference being well-typed in a heap, 
   usually written infix  *)
abstract let contains_a_well_typed (#a:Type) (h:heap) (r:ref a) =
  exists x. h.memory r == Some (| a, x |)

(* An abstract predicate for a reference simply being present in memory, 
   usually written infix *)
abstract let contains (h:heap) (r:nat): GTot Type0 = is_Some (h.memory r)

let contains_a_well_typed_implies_contains (#a:Type) (h:heap) (r:ref a)
    : Lemma (requires (h `contains_a_well_typed` r))
            (ensures (h `contains` (addr r)))
     	    [SMTPatOr [[SMTPat (h `contains_a_well_typed` r)]; [SMTPat (h `contains` (addr r))]]]
    = ()

(* sel: selecting a well-typed reference from a heap *)
abstract let sel (#a:Type) (h:heap) (r:ref a{h `contains_a_well_typed` r})
  : Tot a
  = let Some (| _, x |) = h.memory r in
    x

(* upd: updating a heap at r with x *)
abstract let upd (#a:Type) (h0:heap) (r:ref a{h0 `contains_a_well_typed` r}) (x:a) 
  : Tot heap 
  = { h0 with memory = (fun r' -> if r = r'
			       then Some (| a , x |)
                               else h0.memory r') }

(* alloc: storing x in h0 at a fresh reference *)
abstract let alloc (#a:Type) (h0:heap) (x:a) 
  : Tot (rh1:(ref a * heap))
  = let r  = h0.next_addr in
    let h1 = { next_addr=h0.next_addr + 1; 
   	       memory = (fun r' -> if r = r'
	  	                then Some (| a , x |)
				else h0.memory r') } in
    r, h1

(* modifies s h0 h1: the domain of h1 is no smaller than h0;
		     except for s, every ref in h0 is unmodified in h1 *)
let modifies (s:Set.set nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (h1 `contains_a_well_typed` r)}
                        h0 `contains_a_well_typed` r ==> h1 `contains_a_well_typed` r) /\
  (forall (a:Type) (r:ref a).{:pattern (h1 `contains` (addr r))}
                        h0 `contains` (addr r) ==> h1 `contains` (addr r)) /\
  (forall (a:Type) (r:ref a).{:pattern (sel h1 r)}
                         ~ (Set.mem r s) /\ h0 `contains_a_well_typed` r ==>
                         (sel h1 r == sel h0 r))

(* Now, some properties of all the abstract functions exported by this module *)
(* First, the usual sel/upd properties *)
let sel_upd1 (#a:Type) (h:heap) (r:ref a{h `contains_a_well_typed` r}) (v:a)
    : Lemma (requires True) 
	    (ensures (sel (upd h r v) r == v))
            [SMTPat (sel (upd h r v) r)]
    = ()	      

let sel_upd2 (#a:Type) (#b:Type) (h:heap)
	     (k_1:ref a{h `contains_a_well_typed` k_1})
	     (k_2:ref b{h `contains_a_well_typed` k_2})
	     (v:b)
    : Lemma (requires True) 
	    (ensures (~(k_1 === k_2) ==> sel (upd h k_2 v) k_1 == sel h k_1))
	    [SMTPat (sel (upd h k_2 v) k_1)]
    = ()	      

(* alloc really returns a fresh reference appropriately initialized *)
let alloc_lemma (#a:Type) (h0:heap) (x:a)
    : Lemma (requires (True))
            (ensures (let r, h1 = alloc h0 x in
	              ~ (h0 `contains` r) 
		      /\ h1 `contains_a_well_typed` r
		      /\ sel h1 r == x
		      /\ modifies Set.empty h0 h1
          /\ (forall b (r0 : ref b). (h1 `contains_a_well_typed` r0 /\ addr r0 <> addr r) ==> h0 `contains_a_well_typed` r0)))
	    [SMTPat (alloc h0 x)]
    = ()

(* update preserves a heap's domain *)
let upd_contains (#a:Type) (#b:Type) (h:heap)
		 (k:ref a{h `contains_a_well_typed` k})
		 (r:ref b{h `contains` (addr r)})
		 (v:a)
    : Lemma (requires True) 
	    (ensures ((upd h k v) `contains` (addr r)))
            [SMTPat ((upd h k v) `contains` (addr r))]
    = ()

(* update preserves well-typedness *)
let upd_contains_a_well_typed (#a:Type) (#b:Type) (h:heap)
		 (k:ref a{h `contains_a_well_typed` k})
		 (r:ref b{h `contains_a_well_typed` r})
		 (v:a)
    : Lemma (requires True) 
	    (ensures ((upd h k v) `contains_a_well_typed` r))
            [SMTPat ((upd h k v) `contains_a_well_typed` r)]
    = ()

(* Empty. *)
abstract let emp : heap = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

val in_dom_emp: #a:Type -> k:ref a
                -> Lemma (requires True) (ensures (~ (emp `contains` (addr k))))
		  [SMTPat (emp `contains` (addr k))]
let in_dom_emp #a k = ()

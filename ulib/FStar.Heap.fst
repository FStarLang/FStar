module FStar.Heap

open FStar.Classical

module S   = FStar.Set
module TS  = FStar.TSet
module Seq = FStar.Seq

type set  = Set.set
type tset = TSet.set

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & a))
}

type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

val emp :heap
let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

private type ref' (a:Type0) :Type0 = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}

type ref (a:Type0) = ref' a

val addr_of: #a:Type0 -> ref a -> GTot nat
let addr_of #a r = r.addr

val is_mm: #a:Type0 -> ref a -> GTot bool
let is_mm #a r = r.mm

val compare_addrs: #a:Type0 -> #b:Type0 -> r1:ref a -> r2:ref b -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})
let compare_addrs #a #b r1 r2 = r1.addr = r2.addr

val contains: #a:Type0 -> heap -> ref a -> Type0
let contains #a h r =
  let _ = () in
  Some? (h.memory r.addr) /\ dfst (Some?.v (h.memory r.addr)) == a

val unused_in: #a:Type0 -> ref a -> heap -> Type0
let unused_in #a r h = None? (h.memory r.addr)

let fresh (#a:Type) (r:ref a) (h0:heap) (h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

let only_t (#a:Type0) (x:ref a) = TS.singleton (addr_of x)

let only (#a:Type0) (x:ref a) = S.singleton (addr_of x)

let op_Hat_Plus_Plus (#a:Type0) (r:ref a) (s:set nat) = S.union (only r) s

let op_Plus_Plus_Hat (#a:Type0) (s:set nat) (r:ref a) = S.union s (only r)

let op_Hat_Plus_Hat (#a:Type0) (#b:Type0) (r1:ref a) (r2:ref b) = S.union (only r1) (only r2)

val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a
let sel_tot #a h r =
  let Some (| _, x |) = h.memory r.addr in
  x

(*
 * AR: Flat view change: see the upd function below
 *)
val hsel: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> GTot a
let hsel #a h r = sel_tot h r

val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> a -> Tot heap
let upd_tot #a h r x =
  { h with memory = (fun r' -> if r.addr = r'
			    then Some (| a, x |)
                            else h.memory r') }

(*
 * AR: Flat view change: strong updates are a problem
 * since we may not have allocated enough size in the flat view
 *)
val hupd: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> a -> GTot heap
let hupd #a h r x = upd_tot h r x

val halloc: #a:Type0 -> heap -> a -> mm:bool -> GTot (ref a * heap)
let halloc #a h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r, { h with next_addr = h.next_addr + 1;
              memory = (fun r' -> if r.addr = r'
			then Some (| a, x |)
                        else h.memory r') }

val hfree_mm: #a:Type0 -> h:heap -> r:ref a{h `contains` r /\ is_mm r} -> GTot heap
let hfree_mm #a h r =
  { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

let modifies_t (s:tset nat) (h0:heap) (h1:heap) =
  (forall (a:Type) (r:ref a).{:pattern (hsel h1 r)}
                         ((~ (TS.mem (addr_of r) s)) /\ h0 `contains` r) ==> (h1 `contains` r /\ hsel h1 r == hsel h0 r)) /\
  (forall (a:Type) (r:ref a).{:pattern (contains h1 r)}
                        h0 `contains` r ==> h1 `contains` r) /\
  (forall (a:Type) (r:ref a).{:pattern (r `unused_in` h0)}
                        r `unused_in` h1 ==> r `unused_in` h0)

let modifies (s:set nat) (h0:heap) (h1:heap) = modifies_t (TS.tset_of_set s) h0 h1

let equal_dom (h1:heap) (h2:heap) :GTot Type0 =
  (forall (a:Type0) (r:ref a). h1 `contains` r <==> h2 `contains` r) /\
  (forall (a:Type0) (r:ref a). r `unused_in` h1 <==> r `unused_in` h2)

(***** Flat view changes *****)

type byte

type bytes = Seq.seq byte

assume val b0:byte
assume val b1:byte
assume val b2:byte

assume HasEq_byte: hasEq byte
assume Distinct_bytes: b0 <> b1 /\ b1 <> b2 /\ b2 <> b0

let marshal_bool (b:bool) :(b:bytes)  =
  Seq.create 1 (if b then b1 else b0)

let unmarshal_bool (b:bytes) :option bool =
  if Seq.length b = 1 then
    let b = Seq.index b 0 in
    if b = b1 then Some true
    else if b = b0 then Some false
    else None
  else None

type rtti =
  | Bool

let type_of (r:rtti) :Type =
  match r with
  | Bool -> bool

let size_of (r:rtti) :pos =
  match r with
  | Bool -> 1

let marshal (#r:rtti) (x:type_of r) :(b:bytes{Seq.length b = size_of r}) =
  match r with
  | Bool -> marshal_bool x

let unmarshal (r:rtti) (b:bytes) :option (type_of r) =
  match r with
  | Bool -> unmarshal_bool b

type hi_addr = nat

type lo_addr = nat

type hi_view = heap

type lo_view = lo_addr -> byte

noeq type meta_data = {
  hi_to_lo: hi_addr -> (rtti * lo_addr * lo_addr)
}

noeq type mem' =
  |C: hi:hi_view -> lo:lo_view -> md:meta_data -> mem'

let non_overlapping (a1:nat) (b1:nat{a1 <= b1}) (a2:nat) (b2:nat{a2 <= b2}) :Type0 =
  (a1 < a2 /\ b1 < a2) \/
  (a2 < a1 /\ b2 < a1)

assume val read_lo (lo:lo_view) (lo_start:nat) (lo_end:nat{lo_end >= lo_start})
  :(b:bytes{Seq.length b = lo_end - lo_start + 1 /\
            (forall (i:nat). (i < Seq.length b) ==> Seq.index b i = lo (lo_start + i))})

let wf_mem (m:mem') =
  forall (a:Type0) (r:ref a). m.hi `contains` r ==>
    (let (rtti, lo_start, lo_end) = m.md.hi_to_lo (addr_of r) in
     type_of rtti == a                    /\  //rtti matches the type of the reference
     lo_end - lo_start + 1 = size_of rtti /\  //the range has size per the marshaling of rtti
     read_lo m.lo lo_start lo_end == marshal #rtti (hsel m.hi r) /\  //lo view is in sync with the hi view value
     (forall (b:Type0) (r':ref b). (m.hi `contains` r' /\ addr_of r' <> addr_of r) ==>  //for all other different r'
			      (let (_, lo_start', lo_end') = m.md.hi_to_lo (addr_of r') in
		               lo_start' <= lo_end' /\ non_overlapping lo_start lo_end lo_start' lo_end')))  //the lo-level addresses are non-overlapping

type mem = m:mem'{wf_mem m}




















(*
 * update of a well-typed reference
 *)
private let lemma_upd_contains_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' <==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0  <==> r' `unused_in` h1)))
  = ()

(*
 * update of a reference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:ref a) contains (| b, y:b |),
 * and that (r':ref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (r':ref b). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused reference
 *)
private let lemma_upd_unused_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped reference
 *)
private let lemma_alloc_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let (r, h1) = alloc h0 x mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_free_mm_test (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          r `unused_in` h1 /\
	  (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' <==> h1 `contains` r') /\
				   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc h0 x mm in
          fresh r h0 h1 /\ modifies Set.empty h0 h1)
  = ()

let lemma_contains_implies_used #a h r = ()
let lemma_distinct_addrs_distinct_types #a #b h r1 r2 = ()
let lemma_distinct_addrs_unused #a #b h r1 r2 = ()
let lemma_alloc #a h0 x mm = ()
let lemma_free_mm_sel #a #b h0 r1 r2 = ()
let lemma_free_mm_contains #a #b h0 r1 r2 = ()
let lemma_free_mm_unused #a #b h0 r1 r2 = ()
let lemma_sel_same_addr #a h r1 r2 = ()
let lemma_sel_upd1 #a h r1 x r2 = ()
let lemma_sel_upd2 #a #b h r1 r2 x = ()
let lemma_ref_injectivity = ()
let lemma_in_dom_emp #a r = ()
let lemma_upd_contains #a h r x = ()
let lemma_well_typed_upd_contains #a #b h r1 x r2 = ()
let lemma_unused_upd_contains #a #b h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b h r1 x r2 = ()
let lemma_upd_unused #a #b h r1 x r2 = ()
let lemma_contains_upd_modifies #a h r x = ()
let lemma_unused_upd_modifies #a h r x = ()

let equal h1 h2 =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory
  
let equal_extensional h1 h2 = ()

let upd_upd_same_ref #a h r x y = assert (equal (upd (upd h r x) r y) (upd h r y))

abstract let upd_addr (#a:Type0) (h:heap) (addr:nat) (x:a) :heap =
  let next = if addr >= h.next_addr then addr + 1 else h.next_addr in
  let m = fun r -> if r = addr then Some (| a, x |) else h.memory r in
  { h with next_addr = next; memory = m }

let lemma_upd_addr_sel_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires (addr_of r = addr))
         (ensures  (let h1 = upd_addr h0 addr x in
	            sel h1 r == x))
	 [SMTPat (sel (upd_addr h0 addr x) r)]
  = ()

let lemma_upd_addr_sel_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b)
  :Lemma (requires (addr_of r <> addr))
         (ensures  (let h1 = upd_addr h0 addr x in
		    sel h1 r == sel h0 r))
	 [SMTPat (sel (upd_addr h0 addr x) r)]
  = ()

let lemma_upd_addr_contains_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires (addr_of r = addr))
         (ensures  (let h1 = upd_addr h0 addr x in
                    h1 `contains` r))
	 [SMTPat ((upd_addr h0 addr x) `contains` r)]
  = ()

let lemma_upd_addr_contains_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b)
  :Lemma (requires (addr_of r <> addr))
         (ensures  (let h1 = upd_addr h0 addr x in
	            h1 `contains` r <==> h0 `contains` r))
	 [SMTPat ((upd_addr h0 addr x) `contains` r)]
  = ()

let lemma_upd_addr_unused (#a:Type) (h0:heap) (addr:nat) (x:a) (r:ref a)
  :Lemma (requires True)
         (ensures  ((addr_of r <> addr /\ r `unused_in` h0) <==> r `unused_in` (upd_addr h0 addr x)))
	 [SMTPat (r `unused_in` (upd_addr h0 addr x))]
  = ()

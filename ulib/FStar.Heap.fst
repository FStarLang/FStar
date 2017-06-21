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

abstract type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

abstract val emp :heap
let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

private type ref' (a:Type0) :Type0 = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}

abstract type ref (a:Type0) = ref' a

abstract val addr_of: #a:Type0 -> ref a -> GTot nat
let addr_of #a r = r.addr

abstract val is_mm: #a:Type0 -> ref a -> GTot bool
let is_mm #a r = r.mm

abstract val compare_addrs: #a:Type0 -> #b:Type0 -> r1:ref a -> r2:ref b -> Tot (b:bool{b = (addr_of r1 = addr_of r2)})
let compare_addrs #a #b r1 r2 = r1.addr = r2.addr

abstract val contains: #a:Type0 -> heap -> ref a -> Type0
let contains #a h r =
  let _ = () in
  Some? (h.memory r.addr) /\ dfst (Some?.v (h.memory r.addr)) == a

abstract val unused_in: #a:Type0 -> ref a -> heap -> Type0
let unused_in #a r h = None? (h.memory r.addr)

let fresh (#a:Type) (r:ref a) (h0:heap) (h1:heap) =
  r `unused_in` h0 /\ h1 `contains` r

let only_t (#a:Type0) (x:ref a) = TS.singleton (addr_of x)

let only (#a:Type0) (x:ref a) = S.singleton (addr_of x)

let op_Hat_Plus_Plus (#a:Type0) (r:ref a) (s:set nat) = S.union (only r) s

let op_Plus_Plus_Hat (#a:Type0) (s:set nat) (r:ref a) = S.union s (only r)

let op_Hat_Plus_Hat (#a:Type0) (#b:Type0) (r1:ref a) (r2:ref b) = S.union (only r1) (only r2)

abstract val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a
let sel_tot #a h r =
  let Some (| _, x |) = h.memory r.addr in
  x

(*
 * AR: Flat view change: see the upd function below
 *)
abstract val hsel: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> GTot a
let hsel #a h r = sel_tot h r

abstract val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> a -> Tot heap
let upd_tot #a h r x =
  { h with memory = (fun r' -> if r.addr = r'
			    then Some (| a, x |)
                            else h.memory r') }

(*
 * AR: Flat view change: strong updates are a problem
 * since we may not have allocated enough size in the flat view
 *)
abstract val hupd: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> a -> GTot heap
let hupd #a h r x = upd_tot h r x

abstract val halloc: #a:Type0 -> heap -> a -> mm:bool -> GTot (ref a * heap)
let halloc #a h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r, { h with next_addr = h.next_addr + 1;
              memory = (fun r' -> if r.addr = r'
			then Some (| a, x |)
                        else h.memory r') }

abstract val hfree_mm: #a:Type0 -> h:heap -> r:ref a{h `contains` r /\ is_mm r} -> GTot heap
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

let type_of (r:rtti) :Type0 =
  match r with
  | Bool -> bool

let foo (rt:rtti) (r:ref (type_of rt)) = assert False

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

abstract noeq type meta_data = {
  hi_to_lo: hi_addr -> (t:(rtti * lo_addr * lo_addr){let Mktuple3 _ s e = t in s <= e})
}

private noeq type mem' =
  |C: hi:hi_view -> lo:lo_view -> md:meta_data -> mem'

abstract let non_overlapping (a1:nat) (b1:nat{a1 <= b1}) (a2:nat) (b2:nat{a2 <= b2}) :Type0 = True
  (* (a1 < a2 /\ b1 < a2) \/ *)
  (* (a2 < a1 /\ b2 < a1) *)

assume val read_lo (lo:lo_view) (lo_start:nat) (lo_end:nat{lo_end >= lo_start})
  :(b:bytes{Seq.length b = lo_end - lo_start + 1 /\
            (forall (i:nat). (i < Seq.length b) ==> Seq.index b i = lo (lo_start + i))})

abstract let wf_mem (m:mem') =
  (forall (rt:rtti) (r:ref (type_of rt)). m.hi `contains` r ==>
    (let (rtti', lo_start, lo_end) = m.md.hi_to_lo (addr_of r) in
     rt == rtti'                    /\  //rtti matches the type of the reference
     lo_end - lo_start + 1 = size_of rt /\  //the range has size per the marshaling of rtti
     read_lo m.lo lo_start lo_end == marshal #rt (hsel m.hi r) /\  //lo view is in sync with the hi view value
     (forall (b:Type0) (r':ref b). (m.hi `contains` r' /\ addr_of r' <> addr_of r) ==>  //for all other different r'
			      (let (_, lo_start', lo_end') = m.md.hi_to_lo (addr_of r') in
		               lo_start' <= lo_end' /\ non_overlapping lo_start lo_end lo_start' lo_end'))))  //the lo-level addresses are non-overlapping

abstract type mem = m:mem'{wf_mem m}

abstract let mcontains (#rt:rtti) (m:mem) (r:ref (type_of rt)) = m.hi `contains` r

     (* /\  //lo view is in sync with the hi view value *)
     (* (forall (b:Type0) (r':ref b). (m.hi `contains` r' /\ addr_of r' <> addr_of r) ==>  //for all other different r' *)
     (* 			      (let (_, lo_start', lo_end') = m.md.hi_to_lo (addr_of r') in *)
     (* 		               lo_start' <= lo_end' /\ non_overlapping lo_start lo_end lo_start' lo_end'))))  //the lo-level addresses are non-overlapping *)

private let lemma_mcontains_contains (#rt:rtti) (m:mem) (r:ref (type_of rt))
  :Lemma (requires True)
         (ensures  (m `mcontains` r == m.hi `contains` r))
   [SMTPat (m `mcontains` r)]
  = admit ()

abstract let munused_in (#rt:rtti) (r:ref (type_of rt)) (m:mem) = r `unused_in` m.hi

private let lemma_munused_in_unused_in (#rt:rtti) (r:ref (type_of rt)) (m:mem)
  :Lemma (requires True)
         (ensures  (r `munused_in` m == r `unused_in` m.hi))
   [SMTPat (r `munused_in` m)]
  = admit ()

abstract let get_hi_view (m:mem) :heap = m.hi

let mfresh (#rt:rtti) (r:ref (type_of rt)) (m0:mem) (m1:mem) =
  r `munused_in` m0 /\ m1 `mcontains` r

private let lemma_get_hi_view (m:mem)
  :Lemma (requires True)
         (ensures  (get_hi_view m == m.hi))
   [SMTPat (get_hi_view m)]
  = admit ()

abstract val sel: #rt:rtti -> mem -> ref (type_of rt) -> GTot (type_of rt)
let sel #rt m r = hsel m.hi r

private let lemma_sel_hsel (#rt:rtti) (m:mem) (r:ref (type_of rt))
  :Lemma (requires True)
         (ensures  (sel m r = hsel m.hi r))
   [SMTPat (sel m r)]
  = admit ()

assume val upd: #rt:rtti -> m0:mem -> r:ref (type_of rt){m0 `mcontains` r} -> x:(type_of rt) -> GTot mem
         (* -> GTot (m1:mem{m1.hi = hupd m0.hi r x /\ *)
	 (*                m1.md = m0.md          /\ *)
	 (*                (let (_, lo_start, lo_end) = m0.md.hi_to_lo (addr_of r) in *)
	 (* 		 (read_lo m1.lo lo_start lo_end = marshal #rt x))}) *)

private val lemma_upd_sync:
  #rt:rtti -> m0:mem -> r:ref (type_of rt){m0 `mcontains` r} -> x:(type_of rt)
  -> Lemma (let m1 = upd m0 r x in
           m1.hi == hupd m0.hi r x /\
	   m1.md = m0.md)
    [SMTPat (upd m0 r x)]
let lemma_upd_sync #rt m0 r x = admit ()  //AR: hoping that lemmas for hupd give us framing for other refs in the heap

abstract let get_lo_view (m:mem) :lo_view = m.lo

abstract let get_lo_range (#rt:rtti) (m:mem) (r:ref (type_of rt))
  :GTot (t:(rtti * nat * nat){let Mktuple3 _ s e = t in s <= e})
  = let (rt, s , e) = m.md.hi_to_lo (addr_of r) in
    (rt, s, e)

assume val alloc: #rt:rtti -> m0:mem -> x:(type_of rt) -> mm:bool -> (ref (type_of rt) * mem)
                  (* -> (t:(ref (type_of rt) * mem){let (r, m1) = t in *)
		  (*                               ((r, m1.hi) == halloc #(type_of rt) m0.hi x mm /\ *)
		  (* 		                (forall (a:nat). a <> addr_of r ==> m1.md.hi_to_lo a = m0.md.hi_to_lo a) /\ *)
		  (* 				(let (_, lo_start, lo_end) = m1.md.hi_to_lo (addr_of r) in *)
		  (* 				 read_lo m1.lo lo_start lo_end = marshal #rt x))}) *)

private let lemma_alloc_md_and_sync (#rt:rtti) (m0:mem) (x:type_of rt) (mm:bool)
  :Lemma (requires True)
         (ensures (let r, m1 = alloc m0 x mm in
                   (r, m1.hi) == halloc #(type_of rt) m0.hi x mm /\
		   mfresh r m0 m1 /\
	           (forall (rt:rtti) (r':ref (type_of rt)). addr_of r' <> addr_of r ==> get_lo_range m1 r' == get_lo_range m0 r') /\
	           (forall (rt:rtti) (r:ref (type_of rt)). m0 `mcontains` r ==> m1 `mcontains` r) /\
	           (let (_, lo_start, lo_end) = get_lo_range m1 r in
	            read_lo (get_lo_view m1) lo_start lo_end = marshal #rt x)))
   [SMTPat (alloc m0 x mm)]
  = admit ()

assume val free_mm: #rt:rtti -> m:mem -> r:ref (type_of rt){m `mcontains` r} -> mem

assume val store:
  lo:lo_view -> s:lo_addr -> e:lo_addr{s <= e} -> b:bytes{Seq.length b = e - s + 1} ->
  Tot (r:lo_view{read_lo r s e == b /\
                 (forall (s':lo_addr) (e':lo_addr).
		    (s' <= e' /\ non_overlapping s' e' s e) ==> read_lo lo s' e' == read_lo r s' e')})

assume val sync: m0:mem -> s:set hi_addr -> lo:lo_view -> Tot (option mem)

private let lemma_sync (m0:mem) (s:set hi_addr)  
  (lo:lo_view{let m_lo = get_lo_view m0 in  
              (forall (rt:rtti) (r:ref (type_of rt)). S.mem (addr_of r) s \/
                 (let (_, lo_start, lo_end) = get_lo_range m0 r in
	          read_lo m_lo lo_start lo_end = read_lo lo lo_start lo_end)) /\  //forall references not in the set s, their lo projection remains same as m0, we should be able to derive that their hi projection also remains same from Wf predicate on mem
	      (forall (rt:rtti) (r:ref (type_of rt)).  //and forall references in s, their lo projection in lo can be unmarshaled back to hi view
	         (m0 `mcontains` r /\ S.mem (addr_of r) s) ==>
		 (let (rt, s, e) = get_lo_range m0 r in
		  Some? (unmarshal rt (read_lo lo s e))))})
  :Lemma (requires True)
         (ensures (let m_opt = sync m0 s lo in
	           Some? m_opt /\  //syncing succeeds
                   (let m1 = Some?.v m_opt in
		    get_lo_view m1 == lo /\
                    (forall (rt:rtti) (r:ref (type_of rt)). get_lo_range m0 r == get_lo_range m1 r))))
	 [SMTPat (sync m0 s lo)]
  = admit ()
          
val lemma_contains_implies_used (#rt:rtti) (m:mem) (r:ref (type_of rt))
  :Lemma (requires (m `mcontains` r))
         (ensures  (~ (r `munused_in` m)))
	 [SMTPatOr [[SMTPat (m `mcontains` r)]; [SMTPat (r `munused_in` m)]]]
let lemma_contains_implies_used #rt m r = ()

val lemma_distinct_addrs_distinct_types (#rt_a:rtti) (#rt_b:rtti) (m:mem) (r1:ref (type_of rt_a)) (r2:ref (type_of rt_b))
  :Lemma (requires (rt_a =!= rt_b /\ m `mcontains` r1 /\ m `mcontains` r2))
         (ensures  (addr_of r1 <> addr_of r2))
	 [SMTPatT (m `mcontains` r1); SMTPatT (m `mcontains` r2)]
let lemma_distinct_addrs_distinct_types #rt_a #rt_b m r1 r2 = ()

val lemma_distinct_addrs_unused (#rt_a:rtti) (#rt_b:rtti) (m:mem) (r1:ref (type_of rt_a)) (r2:ref (type_of rt_b))
  :Lemma (requires (r1 `munused_in` m /\ ~ (r2 `munused_in` m)))
         (ensures  (addr_of r1 <> addr_of r2))
         [SMTPat (r1 `munused_in` m); SMTPat (r2 `munused_in` m)]
let lemma_distinct_addrs_unused #rt_a #rt_b m r1 r2 = ()

val lemma_alloc (#rt:rtti) (m0:mem) (x:(type_of rt)) (mm:bool)
  :Lemma (requires True)
         (ensures  (let r, m1 = alloc m0 x mm in
                    mfresh r m0 m1 /\ is_mm r = mm /\ sel m1 r == x /\
		    (forall (rt':rtti) (r':ref (type_of rt')). addr_of r' <> addr_of r ==> sel m1 r' == sel m0 r')))
	 [SMTPat (alloc m0 x mm)]
let lemma_alloc #rt m0 x mm = ()

val lemma_sel_same_addr (rt:rtti) (m:mem) (r1:ref (type_of rt)) (r2:ref (type_of rt))
  :Lemma (requires (m `mcontains` r1 /\ addr_of r1 = addr_of r2))
         (ensures  (m `mcontains` r2 /\ sel m r1 == sel m r2))
	 [SMTPat (sel m r1); SMTPat (sel m r2)]
let lemma_sel_same_addr rt m r1 r2 = ()

val lemma_sel_upd1 (#rt:rtti) (m:mem) (r1:ref (type_of rt){m `mcontains` r1}) (x:(type_of rt)) (r2:ref (type_of rt))
  :Lemma (requires (addr_of r1 = addr_of r2))
         (ensures  (sel (upd m r1 x) r2 == x))
         [SMTPat (sel (upd m r1 x) r2)]
let lemma_sel_upd1 #rt m r1 x r2 = ()

val lemma_sel_upd2 (#rt_a:rtti) (#rt_b:rtti) (m:mem) (r1:ref (type_of rt_a)) (r2:ref (type_of rt_b){m `mcontains` r2}) (x:(type_of rt_b))
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  (sel (upd m r2 x) r1 == sel m r1))
	 [SMTPat (sel (upd m r2 x) r1)]
let lemma_sel_upd2 #rt_a #rt_b m r1 r2 x = ()

val lemma_ref_injectivity
  :(u:unit{forall (rt_a:rtti) (rt_b:rtti) (r1:ref (type_of rt_a)) (r2:ref (type_of rt_b)). rt_a =!= rt_b ==> ~ (eq3 r1 r2)})
let lemma_ref_injectivity = ()

val lemma_in_dom_emp (#rt:rtti) (r:ref (type_of rt))
  :Lemma (requires True)
         (ensures  (r `unused_in` emp))
	 [SMTPat (r `unused_in` emp)]
let lemma_in_dom_emp #rt r = ()

val lemma_upd_contains (#rt:rtti) (m:mem) (r:ref (type_of rt){m `mcontains` r}) (x:(type_of rt))
  :Lemma (requires True)
         (ensures  ((upd m r x) `mcontains` r))
	 [SMTPat ((upd m r x) `mcontains` r)]
let lemma_upd_contains #rt m r x = ()

val lemma_well_typed_upd_contains (#rt_a:rtti) (#rt_b:rtti) (m:mem) (r1:ref (type_of rt_a){m `mcontains` r1}) (x:(type_of rt_a)) (r2:ref (type_of rt_b))
  :Lemma (requires True)
         (ensures  (let m1 = upd m r1 x in
	            m1 `mcontains` r2 <==> m `mcontains` r2))
	 [SMTPat ((upd m r1 x) `mcontains` r2)]
let lemma_well_typed_upd_contains #rt_a #rt_b m r1 x r2 = ()

val lemma_upd_contains_different_addr (#rt_a:rtti) (#rt_b:rtti) (m:mem) (r1:ref (type_of rt_a){m `mcontains` r1}) (x:(type_of rt_a)) (r2:ref (type_of rt_b){m `mcontains` r2})
  :Lemma (requires (addr_of r1 <> addr_of r2))
         (ensures  ((upd m r1 x) `mcontains` r2))
	 [SMTPat ((upd m r1 x) `mcontains` r2)]
let lemma_upd_contains_different_addr #rt_a #rt_b m r1 x r2 = ()


(***** Flat view lemmas *****)

private let lemma_get_lo_range (#rt:rtti) (m:mem) (r:ref (type_of rt))
  :Lemma (requires True)
         (ensures  (let _, s, e = get_lo_range m r in
	            let (_, lo_start, lo_end) = m.md.hi_to_lo r.addr in
		    s == lo_start /\ e == lo_end))
   [SMTPat (get_lo_range m r)]
  = admit ()

let lemma_consistent_views (#rt:rtti) (m:mem) (r:ref (type_of rt){m `mcontains` r})
  :Lemma (let _, s, e = get_lo_range m r in
          read_lo (get_lo_view m) s e = marshal (sel m r))
  = ()

assume Wf_mem:
  (forall (m:mem).
            (forall (rt:rtti) (r:ref (type_of rt)). m `mcontains` r ==>
                                              (let lo = get_lo_view m in
                                               let rt', s, e = get_lo_range m r in
                                               read_lo lo s e == marshal #rt (sel m r) /\
					       rt == rt' /\
					       Some? (unmarshal rt (read_lo lo s e)) /\
					       Some?.v (unmarshal rt (read_lo lo s e)) == sel m r)) /\
	    (forall (rt_a:rtti) (rt_b:rtti) (r1:ref (type_of rt_a)) (r2:ref (type_of rt_b)).
	       (let _, s1, e1 = get_lo_range #rt_a m r1 in
	        let _, s2, e2 = get_lo_range #rt_b m r2 in
		s1 <= e1 /\ s2 <= e2 /\
	        (addr_of r1 <> addr_of r2 ==> non_overlapping s1 e1 s2 e2))))


    (* (let (rtti', lo_start, lo_end) = m.md.hi_to_lo (addr_of r) in *)
    (*  rt == rtti'                    /\  //rtti matches the type of the reference *)
    (*  lo_end - lo_start + 1 = size_of rt /\  //the range has size per the marshaling of rtti *)
    (*  read_lo m.lo lo_start lo_end == marshal #rt (hsel m.hi r))) *)


(* val lemma_contains_upd_modifies (#a:Type0) (h:heap) (r:ref a) (x:a) *)
(*   :Lemma (requires (h `contains` r)) *)
(*          (ensures  (modifies (S.singleton (addr_of r)) h (upd h r x))) *)
(*          [SMTPat (upd h r x); SMTPatT (h `contains` r)] *)

(* val lemma_unused_upd_modifies (#a:Type0) (h:heap) (r:ref a) (x:a) *)
(*   :Lemma (requires (r `unused_in` h)) *)
(*          (ensures  (modifies (Set.singleton (addr_of r)) h (upd h r x))) *)
(*          [SMTPat (upd h r x); SMTPatT (r `unused_in` h)] *)

(* val equal: heap -> heap -> Type0 *)

(* val equal_extensional (h1:heap) (h2:heap) *)
(*   :Lemma (requires True) (ensures (equal h1 h2 <==> h1 == h2)) *)
(*          [SMTPat (equal h1 h2)] *)

(* val upd_upd_same_ref (#a:Type) (h:heap) (r:ref a) (x:a) (y:a) *)
(*   :Lemma (requires True) *)
(*          (ensures  (upd (upd h r x) r y == upd h r y)) *)
(* 	 [SMTPat (upd (upd h r x) r y)] *)


(* (\* *)
(*  * update of a well-typed reference *)
(*  *\) *)
(* private let lemma_upd_contains_test *)
(*   (#a:Type) (h0:heap) (r:ref a) (x:a) *)
(*   :Lemma (h0 `contains` r ==> *)
(*           (let h1 = hupd h0 r x in *)
(*            (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> hsel h0 r' == hsel h1 r') /\ *)
(* 	   (forall (b:Type) (r':ref b). h0 `contains` r' <==> h1 `contains` r')             /\ *)
(* 	   (forall (b:Type) (r':ref b). r' `unused_in` h0  <==> r' `unused_in` h1))) *)
(*   = () *)

(* (\* *)
(*  * update of a reference that is mapped but not necessarily well-typed *)
(*  * we cannot prove that h0 `contains` r' ==> h1 `contains` r' *)
(*  * because consider that in h0 (r:ref a) contains (| b, y:b |), *)
(*  * and that (r':ref b) s.t. r'.addr = r.addr *)
(*  * in h0, r' is well-typed, but in h1 it's not *)
(*  *\) *)
(* private let lemma_upd_contains_not_necessarily_well_typed_test *)
(*   (#a:Type) (h0:heap) (r:ref a) (x:a) *)
(*   :Lemma ((~ (r `unused_in` h0)) ==> *)
(*           (let h1 = hupd h0 r x in *)
(* 	   h1 `contains` r /\ *)
(*            (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> hsel h0 r' == hsel h1 r')           /\ *)
(* 	   (forall (b:Type) (r':ref b). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\ *)
(* 	   (forall (b:Type) (r':ref b). r' `unused_in` h0 <==> r' `unused_in` h1))) *)
(*   = () *)

(* (\* *)
(*  * update of an unused reference *)
(*  *\) *)
(* private let lemma_upd_unused_test *)
(*   (#a:Type) (h0:heap) (r:ref a) (x:a) *)
(*   :Lemma (r `unused_in` h0 ==> *)
(*           (let h1 = upd h0 r x in *)
(* 	   h1 `contains` r /\ *)
(*            (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\ *)
(* 	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\ *)
(* 	   (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))) *)
(*   = () *)

(* (\* *)
(*  * alloc and alloc_mm behaves just like upd of an unmapped reference *)
(*  *\) *)
(* private let lemma_alloc_test (#a:Type) (h0:heap) (x:a) (mm:bool) *)
(*   :Lemma (let (r, h1) = alloc h0 x mm in *)
(*           r `unused_in` h0 /\ *)
(* 	  h1 `contains` r  /\ *)
(*           is_mm r = mm     /\ *)
(*           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\ *)
(*           (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\ *)
(* 	  (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))) *)
(*   = () *)

(* private let lemma_free_mm_test (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r}) *)
(*   :Lemma (let h1 = free_mm h0 r in *)
(*           r `unused_in` h1 /\ *)
(* 	  (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> *)
(* 	                          ((sel h0 r' == sel h1 r'                 /\ *)
(* 				   (h0 `contains` r' <==> h1 `contains` r') /\ *)
(* 				   (r' `unused_in` h0 <==> r' `unused_in` h1))))) *)
(*   = () *)

(* private let lemma_alloc_fresh_test (#a:Type) (h0:heap) (x:a) (mm:bool) *)
(*   :Lemma (let r, h1 = alloc h0 x mm in *)
(*           fresh r h0 h1 /\ modifies Set.empty h0 h1) *)
(*   = () *)

(* let lemma_contains_implies_used #a h r = () *)
(* let lemma_distinct_addrs_distinct_types #a #b h r1 r2 = () *)
(* let lemma_distinct_addrs_unused #a #b h r1 r2 = () *)
(* let lemma_alloc #a h0 x mm = () *)
(* let lemma_free_mm_sel #a #b h0 r1 r2 = () *)
(* let lemma_free_mm_contains #a #b h0 r1 r2 = () *)
(* let lemma_free_mm_unused #a #b h0 r1 r2 = () *)
(* let lemma_sel_same_addr #a h r1 r2 = () *)
(* let lemma_sel_upd1 #a h r1 x r2 = () *)
(* let lemma_sel_upd2 #a #b h r1 r2 x = () *)
(* let lemma_ref_injectivity = () *)
(* let lemma_in_dom_emp #a r = () *)
(* let lemma_upd_contains #a h r x = () *)
(* let lemma_well_typed_upd_contains #a #b h r1 x r2 = () *)
(* let lemma_unused_upd_contains #a #b h r1 x r2 = () *)
(* let lemma_upd_contains_different_addr #a #b h r1 x r2 = () *)
(* let lemma_upd_unused #a #b h r1 x r2 = () *)
(* let lemma_contains_upd_modifies #a h r x = () *)
(* let lemma_unused_upd_modifies #a h r x = () *)

(* let equal h1 h2 = *)
(*   let _ = () in *)
(*   h1.next_addr = h2.next_addr /\ *)
(*   FStar.FunctionalExtensionality.feq h1.memory h2.memory *)
  
(* let equal_extensional h1 h2 = () *)

(* let upd_upd_same_ref #a h r x y = assert (equal (upd (upd h r x) r y) (upd h r y)) *)

(* abstract let upd_addr (#a:Type0) (h:heap) (addr:nat) (x:a) :heap = *)
(*   let next = if addr >= h.next_addr then addr + 1 else h.next_addr in *)
(*   let m = fun r -> if r = addr then Some (| a, x |) else h.memory r in *)
(*   { h with next_addr = next; memory = m } *)

(* let lemma_upd_addr_sel_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a) *)
(*   :Lemma (requires (addr_of r = addr)) *)
(*          (ensures  (let h1 = upd_addr h0 addr x in *)
(* 	            sel h1 r == x)) *)
(* 	 [SMTPat (sel (upd_addr h0 addr x) r)] *)
(*   = () *)

(* let lemma_upd_addr_sel_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b) *)
(*   :Lemma (requires (addr_of r <> addr)) *)
(*          (ensures  (let h1 = upd_addr h0 addr x in *)
(* 		    sel h1 r == sel h0 r)) *)
(* 	 [SMTPat (sel (upd_addr h0 addr x) r)] *)
(*   = () *)

(* let lemma_upd_addr_contains_same_addr (#a:Type0) (h0:heap) (addr:nat) (x:a) (r:ref a) *)
(*   :Lemma (requires (addr_of r = addr)) *)
(*          (ensures  (let h1 = upd_addr h0 addr x in *)
(*                     h1 `contains` r)) *)
(* 	 [SMTPat ((upd_addr h0 addr x) `contains` r)] *)
(*   = () *)

(* let lemma_upd_addr_contains_different_addr (#a:Type0) (#b:Type0) (h0:heap) (addr:nat) (x:a) (r:ref b) *)
(*   :Lemma (requires (addr_of r <> addr)) *)
(*          (ensures  (let h1 = upd_addr h0 addr x in *)
(* 	            h1 `contains` r <==> h0 `contains` r)) *)
(* 	 [SMTPat ((upd_addr h0 addr x) `contains` r)] *)
(*   = () *)

(* let lemma_upd_addr_unused (#a:Type) (h0:heap) (addr:nat) (x:a) (r:ref a) *)
(*   :Lemma (requires True) *)
(*          (ensures  ((addr_of r <> addr /\ r `unused_in` h0) <==> r `unused_in` (upd_addr h0 addr x))) *)
(* 	 [SMTPat (r `unused_in` (upd_addr h0 addr x))] *)
(*   = () *)

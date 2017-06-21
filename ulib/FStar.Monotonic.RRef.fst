module FStar.Monotonic.RRef

open FStar
open FStar.HyperHeap

open FStar.ST
open FStar.HyperStack

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let reln (a:Type) = a -> a -> Type

let monotonic (a:Type) (b:reln a) =
  (forall x. b x x)                             (* reflexive *)
  /\ (forall x y z. b x y /\ b y z ==> b x z)   (* transitive *)

(*
 * AR: adding is_eternal_region refinement, since mrefs are allocated using ralloc
 *)
type rid = r:HH.rid{is_eternal_region r}

(*
 * AR: HS.ref, means it is not mm.
 * This along with rid above is essential to justify recall.
 *)
abstract type m_rref (r:rid) (a:Type) (b:reln a) = x:HS.ref a{x.id = r}

(* let haseq_m_rref (r:rid) (a:Type) (b:reln a)  *)
(*     : Lemma (requires True) *)
(* 	    (ensures (hasEq (m_rref r a b))) *)
(* 	    [SMTPat (hasEq (m_rref r a b))] *)
(*     = () *)

(* val as_rref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (rref r a) *)
(* let as_rref #r #a #b x = x *)

(* assume HasEq_m_rref: forall (r:rid) (a:Type) (b:reln a).{:pattern (hasEq (m_rref r a b))} hasEq (m_rref r a b) *)
(*
 * AR: the refinement is important here, for as_rref rid was part of the type index
 *)
val as_hsref: #r:rid -> #a:Type -> #b:reln a -> m_rref r a b -> GTot (x:HS.ref a{x.id = r})
let as_hsref #r #a #b x = x

(* val m_contains : #r:rid -> #a:Type -> #b:reln a -> mr:m_rref r a b -> m:t -> GTot bool *)
(* let m_contains #r #a #b mr m = HyperHeap.contains_ref (as_rref mr) m *)

let m_contains (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.contains m (as_hsref mr)

let m_unused_in (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m:mem) = HS.unused_in (as_hsref mr) m

(* let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:t) (m1:t) : GTot Type0 = *)
(*   HyperHeap.fresh_rref (as_rref mr) m0 m1 *)

let m_fresh (#r:rid) (#a:Type) (#b:reln a) (mr:m_rref r a b) (m0:mem) (m1:mem) : GTot Type0 =
  let hsref = as_hsref mr in
  HyperHeap.fresh_rref hsref.ref m0.h m1.h

(* val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> GTot a *)
(* let m_sel #r #a #b h m = HyperHeap.sel h (as_rref m) *)

val m_sel: #r:rid -> #a:Type -> #b:reln a -> h:mem -> m_rref r a b -> GTot a
let m_sel #r #a #b h m = HS.sel h (as_hsref m)

(* 17-01-05 m_upd seems unsound (2 missing preconditions) and unused: commenting out for now 
(* val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:t -> m_rref r a b -> a -> GTot t *)
(* let m_upd #r #a #b h m v = HyperHeap.upd h (as_rref m) v *)

val m_upd: #r:rid -> #a:Type -> #b:reln a -> h:mem{live_region h r} -> m_rref r a b -> a -> GTot mem
let m_upd #r #a #b h m v = HS.upd h (as_hsref m) v
*)

(* allocates a reference and an associated monotonic-update condition *)
val m_alloc: #a:Type
          -> #b:reln a
	    -> r:rid
            -> init:a
            -> ST (m_rref r a b)
		(requires (fun _ -> monotonic a b))
		(ensures (fun h0 (m:m_rref r a b) h1 -> ralloc_post r init h0 (as_hsref m) h1))
let m_alloc #a #b r init = ST.ralloc r init

val m_read:#r:rid 
       -> #a:Type
       -> #b:reln a
       -> x:m_rref r a b
       -> ST a
            (requires (fun h -> True))
            (ensures (deref_post (as_hsref x)))
let m_read #r #a #b x = !x

val m_write:#r:rid 
        -> #a:Type
        -> #b:reln a
        -> x:m_rref r a b
        -> v:a
        -> ST unit
              (requires (fun h0 -> h0 `contains` (as_hsref x) /\ b (m_sel h0 x) v))
              (ensures (assign_post (as_hsref x) v))
let m_write #r #a #b x v = x := v

(* states that p is preserved by any valid updates on r; note that h0 and h1 may differ arbitrarily elsewhere, hence proving stability usually requires that p depends only on r's content. 
*)
unfold type stable_on_t (#i:rid) (#a:Type) (#b:reln a) (r:m_rref i a b) (p:(mem -> GTot Type0)) =
  forall h0 h1. p h0 /\ b (m_sel h0 r) (m_sel h1 r) ==> p h1

abstract type witnessed (p:(mem -> GTot Type0)) = True

(* witnesses a property stable by all updates on p; once we have a witness, there is no need to record that it was obtained using m's monotonicity. *) 
val witness: #r:rid
          -> #a:Type
          -> #b:reln a
          -> m:m_rref r a b
          -> p:(mem -> GTot Type0)
          -> ST unit
                (requires (fun h0 -> p h0 /\ stable_on_t m p))
                (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #r #a #b m p = ()

assume val weaken_witness : p:(mem -> GTot Type0) 
			  -> q:(mem -> GTot Type0) 
			  -> Lemma
  ((forall h. p h ==> q h) /\ witnessed p ==> witnessed q)

(* claims a witnessed property holds in the current state *)
val testify: p:(mem -> GTot Type0)
          -> ST unit
               (requires (fun _ ->  witnessed p))
               (ensures (fun h0 _ h1 -> h0==h1 /\ p h1))
let testify p = admit() //intentionally admitted

(* 17-01-05 can we prove it from testify? *) 
val testify_forall: #a:Type -> #p:(a -> mem -> Type0) 
       -> $s:squash (forall (x:a). witnessed (p x)) 
       -> ST unit
  (requires (fun h -> True))
  (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:a). p x h1)))
let testify_forall #a #p $s = admit() //intentionally admitted

val m_recall: #r:rid -> #a:Type -> #b:reln a 
            -> m:m_rref r a b
	    -> ST unit 
	      (requires (fun h -> True))
	      (ensures (fun h0 _ h1 -> h0==h1 /\ m_contains m h1))
let m_recall #r #a #b m = recall m

(* another instance of monotonic property, this time on the global map of regions; not used much? *)
let rid_exists (r:rid) (h:mem) = b2t(Map.contains h.h r)
// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{witnessed (rid_exists r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun h -> True)
  (fun h0 r' h1 -> r=r' /\ h0==h1)

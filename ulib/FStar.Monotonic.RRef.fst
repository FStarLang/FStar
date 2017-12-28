module FStar.Monotonic.RRef

open FStar.Preorder

open FStar.HyperStack
open FStar.HyperStack.ST

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

type rid = r:rid{is_eternal_region r}

unfold type stable_on_t (#i:rid) (#a:Type) (#b:preorder a) (r:m_rref i a b) (p:HST.mem_predicate)
  = HST.stable_on_t #i #a #b r p

(* witnesses a property stable by all updates on p; once we have a witness, there is no need to record that it was obtained using m's monotonicity. *) 
val witness (#r:rid) (#a:Type) (#b:preorder a) (m:m_rref r a b) (p:HST.mem_predicate)
  :ST unit
      (requires (fun h0      -> p h0   /\ stable_on_t m p))
      (ensures  (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness #r #a #b m p = HST.mr_witness m p

(* claims a witnessed property holds in the current state *)
val testify (p:mem_predicate)
  :ST unit (requires (fun _      ->  witnessed p))
           (ensures (fun h0 _ h1 -> h0==h1 /\ p h1))
let testify p = HST.gst_recall p

(* 17-01-05 can we prove it from testify? *) 
val testify_forall (#c:Type) (#p:(c -> mem -> Type0))
  ($s:squash (forall (x:c). witnessed (p x)))
  :ST unit (requires (fun h      -> True))
           (ensures (fun h0 _ h1 -> h0==h1 /\ (forall (x:c). p x h1)))
let testify_forall #c #p $s = admit ()

(* another instance of monotonic property, this time on the global map of regions; not used much? *)
let rid_exists (r:rid) (h:mem) = region_contains_pred r h
// ex_rid: The type of a region id that is known to exist now and for ever more
type ex_rid = r:rid{HST.witnessed (region_contains_pred r)}

assume val ex_rid_of_rid: r:rid -> ST ex_rid
  (fun h -> True)
  (fun h0 r' h1 -> r=r' /\ h0==h1)

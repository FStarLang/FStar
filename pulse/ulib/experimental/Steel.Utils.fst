module Steel.Utils
open Steel.Memory
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

let elim_pure_alt (p:prop)
  : SteelT (_:unit{p}) (pure p) (fun _ -> emp)
  = Steel.Effect.Atomic.elim_pure p

let elim_pure (p:prop)
  : Steel unit (pure p) (fun _ -> emp)
   (requires fun _ -> True)
   (ensures fun _ _ _ -> p)
  = let x = elim_pure_alt p in
    ()

let lift_lemma_alt (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : SteelT (_:unit{q}) p (fun _ -> p)
  = Steel.Effect.Atomic.lift_lemma p q l

let lift_lemma (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : Steel unit p (fun _ -> p) (requires fun _ -> True) (ensures fun _ _ _ -> q)
  = let _ = lift_lemma_alt p q l in ()

let pts_to_not_null (#a:Type)
                    (#[@@@ framing_implicit] p:perm)
                    (#[@@@ framing_implicit] v:FStar.Ghost.erased a)
                    (r:ref a)
  : Steel unit
    (pts_to r p v)
    (fun _ -> pts_to r p v)
    (fun _ -> True)
    (fun _ _ _ -> r =!= null)
  = lift_lemma (pts_to r p v) (r =!= null) (fun m -> Steel.Reference.pts_to_not_null r p v m)

let change_slprop_ens (p:slprop) (q:slprop) (r:prop) (f:(m:mem -> Lemma (requires interp p m)
                                                                       (ensures interp q m /\ r)))
  : Steel unit p (fun _ -> q) (requires fun _ -> True) (ensures fun _ _ _ -> r)
  = Steel.Effect.change_slprop p (q `star` pure r)
                                 (fun m -> f m;
                                        Steel.Memory.emp_unit q;
                                        Steel.Memory.pure_star_interp q r m);
    elim_pure r


let pure_as_ens (#[@@@framing_implicit] p:prop) ()
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = change_slprop_ens (pure p) (pure p) p (Steel.Memory.pure_interp p)

let slassert (p:slprop)
  : SteelT unit p (fun _ -> p)
  = noop()

let pts_to_injective_eq #a #p #q (r:ref a) (v0 v1:Ghost.erased a)
  : Steel unit (pts_to r p v0 `star` pts_to r q v1)
               (fun _ -> pts_to r p v0 `star` pts_to r q v0)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> v0 == v1)
  = change_slprop_ens (pts_to r p v0 `star` pts_to r q v1)
                      (pts_to r p v0 `star` pts_to r q v0)
                      (v0 == v1)
                      (pts_to_ref_injective r p q v0 v1)

module H = Steel.HigherReference
let higher_ref_pts_to_injective_eq #a #p #q (r:H.ref a) (v0 v1:Ghost.erased a)
  : Steel unit (H.pts_to r p v0 `star` H.pts_to r q v1)
               (fun _ -> H.pts_to r p v0 `star` H.pts_to r q v0)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> v0 == v1)
  = let open H in
    change_slprop_ens (pts_to r p v0 `star` pts_to r q v1)
                      (pts_to r p v0 `star` pts_to r q v0)
                      (v0 == v1)
                      (pts_to_ref_injective r p q v0 v1)

let rewrite #a (#[@@@framing_implicit]p:a -> slprop)(x y:a)
  : Steel unit (p x) (fun _ -> p y)
    (requires fun _ -> x == y)
    (ensures fun _ _ _ -> True)
  = Steel.Effect.change_slprop (p x) (p y) (fun _ -> ())

let extract_pure (p:prop)
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = elim_pure p;
    Steel.Effect.intro_pure p

let dup_pure (p:prop)
  : SteelT unit (pure p) (fun _ -> pure p `star` pure p)
  = extract_pure p;
    Steel.Effect.intro_pure p

let emp_unit (p:slprop)
  : Lemma (((p `star` emp) `equiv` p) /\
           ((emp `star` p) `equiv` p))
          [SMTPatOr [[SMTPat (p `star` emp)];
                     [SMTPat (emp `star` p)]]]
  = Steel.Memory.emp_unit p;
    Steel.Memory.star_commutative emp p

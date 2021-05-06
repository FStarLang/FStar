module Steel.Utils
open Steel.Memory
open Steel.Effect.Atomic
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
  = let x = Steel.Effect.Atomic.elim_pure p in
    ()

let lift_lemma_alt (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : SteelT (_:unit{q}) p (fun _ -> p)
  = Steel.Effect.Atomic.lift_lemma p q l

let lift_lemma (p:slprop) (q:prop) (l:(hmem p -> Lemma q))
  : Steel unit p (fun _ -> p) (requires fun _ -> True) (ensures fun _ _ _ -> q)
  = let _ = lift_lemma_alt p q l in ()

let pts_to_not_null (#a:Type)
                    (#opened:inames)
                    (#p:perm)
                    (#v:FStar.Ghost.erased a)
                    (r:ref a)
  : SteelGhost unit opened
    (pts_to r p v)
    (fun _ -> pts_to r p v)
    (fun _ -> True)
    (fun _ _ _ -> r =!= null)
  = Steel.Effect.Atomic.extract_info (pts_to r p v) (r =!= null)
      (fun m -> Steel.Reference.pts_to_not_null r p v m)

let change_slprop_ens (p:slprop) (q:slprop) (r:prop) (f:(m:mem -> Lemma (requires interp p m)
                                                                       (ensures interp q m /\ r)))
  : Steel unit p (fun _ -> q) (requires fun _ -> True) (ensures fun _ _ _ -> r)
  = change_slprop p (q `star` pure r)
                                 (fun m -> f m;
                                        Steel.Memory.emp_unit q;
                                        Steel.Memory.pure_star_interp q r m);
    elim_pure r


let pure_as_ens (#p:prop) ()
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = change_slprop_ens (pure p) (pure p) p (Steel.Memory.pure_interp p)

let slassert (p:slprop)
  : SteelT unit p (fun _ -> p)
  = noop (); ()

let rewrite #a (#p:a -> slprop)(x y:a)
  : Steel unit (p x) (fun _ -> p y)
    (requires fun _ -> x == y)
    (ensures fun _ _ _ -> True)
  = change_slprop (p x) (p y) (fun _ -> ())

let extract_pure (p:prop)
  : Steel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = elim_pure p;
    intro_pure p

let dup_pure (p:prop)
  : SteelT unit (pure p) (fun _ -> pure p `star` pure p)
  = extract_pure p;
    intro_pure p

let emp_unit (p:slprop)
  : Lemma (((p `star` emp) `equiv` p) /\
           ((emp `star` p) `equiv` p))
          [SMTPatOr [[SMTPat (p `star` emp)];
                     [SMTPat (emp `star` p)]]]
  = Steel.Memory.emp_unit p;
    Steel.Memory.star_commutative emp p

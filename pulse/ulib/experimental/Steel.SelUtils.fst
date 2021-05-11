module Steel.SelUtils
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.FractionalPermission
open Steel.SelReference

let pts_to_not_null (#a:Type)
                    (#opened:inames)
                    (#p:perm)
                    (#v:FStar.Ghost.erased a)
                    (r:ref a)
  : SteelSelGhost unit opened
    (pts_to r p v)
    (fun _ -> pts_to r p v)
    (fun _ -> True)
    (fun _ _ _ -> r =!= null)
  = extract_info_raw (pts_to r p v) (r =!= null)
      (fun m -> pts_to_not_null r p v m)

let change_slprop_ens (p:vprop) (q:vprop) (r:prop) (f:(m:mem -> Lemma (requires interp (hp_of p) m)
                                                                       (ensures interp (hp_of q) m /\ r)))
  : SteelSel unit p (fun _ -> q) (requires fun _ -> True) (ensures fun _ _ _ -> r)
  = rewrite_slprop p (q `star` pure r)
                                 (fun m -> f m;
                                        Steel.Memory.emp_unit (hp_of q);
                                        Steel.Memory.pure_star_interp (hp_of q) r m);
    elim_pure r

let pure_as_ens (#p:prop) ()
  : SteelSel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = change_slprop_ens (pure p) (pure p) p (Steel.Memory.pure_interp p)

let rewrite #a (#p:a -> vprop) (x y:a)
  : SteelSel unit (p x) (fun _ -> p y)
    (requires fun _ -> x == y)
    (ensures fun _ _ _ -> True)
  = rewrite_slprop (p x) (p y) (fun _ -> ())

let extract_pure (p:prop)
  : SteelSel unit (pure p) (fun _ -> pure p) (fun _ -> True) (fun _ _ _ -> p)
  = elim_pure p;
    intro_pure p

let dup_pure (p:prop)
  : SteelSelT unit (pure p) (fun _ -> pure p `star` pure p)
  = extract_pure p;
    intro_pure p

let emp_unit (p:vprop)
  : Lemma (((p `star` emp) `equiv` p) /\
           ((emp `star` p) `equiv` p))
          [SMTPatOr [[SMTPat (p `star` emp)];
                     [SMTPat (emp `star` p)]]]
  = reveal_equiv (p `star` emp) p;
    reveal_equiv (emp `star` p) p;
    reveal_emp ();
    Steel.Memory.emp_unit (hp_of p);
    Steel.Memory.star_commutative Steel.Memory.emp (hp_of p)

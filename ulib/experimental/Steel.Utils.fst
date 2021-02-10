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
                    (#[@@framing_implicit] p:perm)
                    (#[@@framing_implicit] v:FStar.Ghost.erased a)
                    (r:ref a)
  : Steel unit
    (pts_to r p v)
    (fun _ -> pts_to r p v)
    (fun _ -> True)
    (fun _ _ _ -> r =!= null)
  = lift_lemma (pts_to r p v) (r =!= null) (fun m -> Steel.Reference.pts_to_not_null r p v m)

module Pulse.Lib.Forall
open Pulse.Main
open Pulse.Lib.Core
module F = FStar.FunctionalExtensionality

let token (v:vprop) = v

let universal_quantifier #a (v:vprop) (p: a -> vprop) =
  x:a -> stt_ghost unit v (fun _ -> p x)

let is_forall #a (v:vprop) (p:a -> vprop) =
  squash (universal_quantifier #a v p)

let uquant (#a:Type u#a) (p: a -> vprop)
: vprop
= exists* (v:vprop).
    pure (is_forall v p) **
    token v
let ( forall* ) (#a:Type u#a) (p:a -> vprop) = uquant #a (F.on_dom a p)

let extract_q #a (v:vprop) (p:a -> vprop) (pf:squash (is_forall v p))
: universal_quantifier #a v p
= let f
    : squash (universal_quantifier #a v p)
    = FStar.Squash.join_squash pf
  in
  let f : squash (exists (x:universal_quantifier #a v p). True)
    = FStar.Squash.bind_squash f
        (fun x -> 
          (introduce exists (x:universal_quantifier #a v p). True
           with x
           and ()))
  in
  let x:Ghost.erased (universal_quantifier #a v p) = 
    FStar.IndefiniteDescription.indefinite_description_tot
      (universal_quantifier #a v p)
      (fun x -> True)
  in
  Ghost.reveal x

```pulse
ghost
fn return (#a:Type u#2) (x:a)
requires emp
returns v:a
ensures pure (v == x)
{
  x
}
```


```pulse
ghost
fn elim_forall'
    (#a:Type u#0)
    (#p:a->vprop)
    (x:a)
requires forall* (x:a). p x
ensures p x
{
    unfold (forall* x. p x);
    unfold (uquant #a (F.on_dom a (fun x -> p x)));
    with v. assert (token v);
    unfold token;
    let f = return (extract_q (Ghost.reveal v) (F.on_dom a (fun x -> p x)) ());
    f x;
    rewrite ((F.on_dom a (fun x -> p x)) x) as (p x);
}
```

let elim_forall
    (#a:Type u#a)
    (#p:a->vprop)
    (x:a)
: stt_ghost unit
    (forall* (x:a). p x)
    (fun _ -> p x)
= let m1 = elim_exists #vprop (fun (v:vprop) -> pure (is_forall v p) ** token v) in
  let m2 (v:Ghost.erased vprop)
    : stt_ghost unit 
        (pure (is_forall v p) ** token v)
        (fun _ -> p x)
    = bind_ghost
          (frame_ghost 
          (token v)
          (elim_pure_explicit (is_forall v p)))
        (fun (pf:squash (is_forall v p)) ->
          let f = extract_q v p pf in
          sub_ghost (emp ** Ghost.reveal v)
                    (fun _ -> p x)
                    (vprop_equiv_sym _ _ (vprop_equiv_unit _))
                    (intro_vprop_post_equiv 
                          (fun _ -> p x)
                          (fun _ -> p x)
                          (fun _ -> vprop_equiv_refl (p x)))
                        (f x))
  in
  bind_ghost m1 m2

let intro_forall
    (#a:Type)
    (#p:a->vprop)
    (v:vprop)
    (f_elim : (x:a -> stt_ghost unit v (fun _ -> p x)))
: stt_ghost unit
    v
    (fun _ -> forall* x. p x)
= let _ : squash (universal_quantifier v p) = FStar.Squash.return_squash f_elim in
  let m1
    : stt_ghost unit (emp ** v) (fun _ -> pure (is_forall v p) ** v) 
    = frame_ghost v (intro_pure (is_forall v p) ()) in
  let m2 ()
    : stt_ghost unit
          (pure (is_forall v p) ** token v) 
          (fun _ -> forall* x. p x)
    = intro_exists (fun (v:vprop) -> pure (is_forall v p) ** token v) v
  in
  let m = bind_ghost m1 m2 in
  sub_ghost v _
            (vprop_equiv_unit _)
            (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
            m
   
let vprop_equiv_forall
    (#a:Type)
    (p q: a -> vprop)
    (_:squash (forall x. p x == q x))
: vprop_equiv (op_forall_Star p) (op_forall_Star q)
= FStar.FunctionalExtensionality.extensionality _ _ p q;
  vprop_equiv_refl (op_forall_Star p)
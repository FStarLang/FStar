module Pulse.Lib.Forall
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
module F = FStar.FunctionalExtensionality

let token (v:slprop) = v

let universal_quantifier #a (v:slprop) (p: a -> slprop) =
  x:a -> stt_ghost unit emp_inames v (fun _ -> p x)

let is_forall #a (v:slprop) (p:a -> slprop) =
  squash (universal_quantifier #a v p)

let uquant (#a:Type u#a) (p: a -> slprop)
: slprop
= exists* (v:slprop).
    pure (is_forall v p) **
    token v
let ( forall* ) (#a:Type u#a) (p:a -> slprop) = uquant #a (F.on_dom a p)

let extract_q #a (v:slprop) (p:a -> slprop) (pf:squash (is_forall v p))
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


ghost
fn elim_forall'
    (#a:Type u#0)
    (#p:a->slprop)
    (x:a)
requires forall* (x:a). p x
ensures p x
{
    unfold (forall* x. p x);
    unfold (uquant #a (F.on_dom a (fun x -> p x)));
    with v. assert (token v);
    unfold token;
    let f = extract_q (Ghost.reveal v) (F.on_dom a (fun x -> p x)) ();
    f x;
    rewrite ((F.on_dom a (fun x -> p x)) x) as (p x);
}


let elim_forall
    (#a:Type u#a)
    (#p:a->slprop)
    (x:a)
: stt_ghost unit emp_inames
    (forall* (x:a). p x)
    (fun _ -> p x)
= let m1 = elim_exists #slprop (fun (v:slprop) -> pure (is_forall v p) ** token v) in
  let m2 (v:Ghost.erased slprop)
    : stt_ghost unit emp_inames
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
                    (slprop_equiv_sym _ _ (slprop_equiv_unit _))
                    (intro_slprop_post_equiv 
                          (fun _ -> p x)
                          (fun _ -> p x)
                          (fun _ -> slprop_equiv_refl (p x)))
                        (f x))
  in
  bind_ghost m1 m2

let intro_forall
    (#a:Type)
    (#p:a->slprop)
    (v:slprop)
    (f_elim : (x:a -> stt_ghost unit emp_inames v (fun _ -> p x)))
: stt_ghost unit emp_inames
    v
    (fun _ -> forall* x. p x)
= let _ : squash (universal_quantifier v p) = FStar.Squash.return_squash f_elim in
  let m1
    : stt_ghost unit emp_inames (emp ** v) (fun _ -> pure (is_forall v p) ** v) 
    = frame_ghost v (intro_pure (is_forall v p) ()) in
  let m2 ()
    : stt_ghost unit emp_inames
          (pure (is_forall v p) ** token v) 
          (fun _ -> forall* x. p x)
    = intro_exists (fun (v:slprop) -> pure (is_forall v p) ** token v) v
  in
  let m = bind_ghost m1 m2 in
  sub_ghost v _
            (slprop_equiv_unit _)
            (intro_slprop_post_equiv _ _ (fun _ -> slprop_equiv_refl _))
            m
   
let slprop_equiv_forall
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. p x == q x))
: slprop_equiv (op_forall_Star p) (op_forall_Star q)
= FStar.FunctionalExtensionality.extensionality _ _ p q;
  slprop_equiv_refl (op_forall_Star p)

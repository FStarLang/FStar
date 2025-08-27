module Pulse.Lib.Forall
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
module F = FStar.FunctionalExtensionality

let token (v:slprop) = v

let is_forall #a (v:slprop) (p:a -> slprop) =
  squash (forall_f p #v)

let uquant (#a:Type u#a) (p: a -> slprop)
: slprop
= exists* (v:slprop).
    pure (is_forall v p) **
    token v
let ( forall* ) (#a:Type u#a) (p:a -> slprop) = uquant #a (F.on_dom a p)

let extract_q #a (v:slprop) (p:a -> slprop) (pf:squash (is_forall v p))
: forall_f p #v
= let f
    : squash (forall_f p #v)
    = FStar.Squash.join_squash pf
  in
  let f : squash (exists (x: forall_f p #v). True)
    = FStar.Squash.bind_squash f
        (fun x -> 
          (introduce exists (x: forall_f p #v). True
           with x
           and ()))
  in
  let x:Ghost.erased (forall_f p #v) = 
    FStar.IndefiniteDescription.indefinite_description_tot
      (forall_f p #v)
      (fun x -> True)
  in
  Ghost.reveal x


ghost
fn elim_forall u#a
  (#a : Type u#a)
  (#p : a->slprop)
  (x : a)
  requires forall* x. p x
  ensures  p x
{
  unfold (forall* x. p x);
  unfold uquant (F.on_dom a (fun x -> p x));
  with v. assert token v; unfold token v;
  extract_q v (F.on_domain a (fun x -> p x)) () x;
}

ghost
fn intro_forall u#a
  (#a:Type u#a)
  (#p:a->slprop)
  (v:slprop)
  (f_elim : forall_f #a p #v)
  requires v
  ensures  forall* x. p x
{
  let f_elim : forall_f (F.on_dom a (fun x -> p x)) #v =
    (fun x -> f_elim x);
  Squash.return_squash f_elim;
  fold token v;
  fold uquant (F.on_dom a (fun x -> p x));
  fold (forall* x. p x);
}

let slprop_equiv_forall
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. p x == q x))
: slprop_equiv (op_forall_Star p) (op_forall_Star q)
= FStar.FunctionalExtensionality.extensionality _ _ p q;
  slprop_equiv_refl (op_forall_Star p)

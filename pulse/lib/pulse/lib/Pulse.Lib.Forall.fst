module Pulse.Lib.Forall
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
open FStar.Nonempty
module F = FStar.FunctionalExtensionality

let token (v:slprop) = v

let is_forall #a (v:slprop) (p:a -> slprop) =
  nonempty (forall_f p #v)

let uquant (#a:Type u#a) (p: a -> slprop)
: slprop
= exists* (v:slprop).
    pure (is_forall v p) **
    token v
let ( forall* ) (#a:Type u#a) (p:a -> slprop) = uquant #a (F.on_dom a p)

let extract_q #a (v:slprop) (p:a -> slprop) (pf:is_forall v p)
: forall_f p #v
= nonempty_elim' pf


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
  with v. unfold token v;
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
  nonempty_intro f_elim;
  fold token v;
  fold uquant (F.on_dom a (fun x -> p x));
  fold (forall* x. p x);
}

fn introducable_forall_aux u#a u#b (a: Type u#a) (t: a -> Type u#b) is extra (concl: a -> slprop)
      {| (x:a -> introducable emp_inames extra (concl x) (t x)) |}
      (k: (x:a -> t x)) :
    stt_ghost unit is extra (fun _ -> forall* x. concl x) = {
  intro_forall #a #concl extra fn x {
    intro (concl x) #extra (fun _ -> k x)
  }
}

instance introducable_forall (a: Type u#a) (t: a -> Type u#b) is extra concl {| (x:a -> introducable emp_inames extra (concl x) (t x)) |} :
    introducable is extra (forall* x. concl x) (x:a -> t x) =
  { intro_aux = introducable_forall_aux a t is extra concl }

let slprop_equiv_forall
    (#a:Type)
    (p q: a -> slprop)
    (_:squash (forall x. p x == q x))
: slprop_equiv (op_forall_Star p) (op_forall_Star q)
= FStar.FunctionalExtensionality.extensionality _ _ p q;
  slprop_equiv_refl (op_forall_Star p)

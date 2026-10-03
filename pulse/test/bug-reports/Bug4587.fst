module Bug4587

(* FStarLang/FStar#4587: when the unifier solves a non-pattern flex term by
   the quasi-pattern rule, the uvars on the RHS must stay abstracted over the
   pattern variables (here, the existential [_v7] opened by [havoc]). *)
#lang-pulse
open Pulse
module R = Pulse.Lib.Reference

let eta_expanded (#[@@@mkey] t: Type0) (x: t) : slprop = emp

[@@pulse_eager_intro]
ghost fn eta_expanded_leaf (#t: Type0) (x: t)
  ensures eta_expanded x
{ fold eta_expanded x }

[@@pulse_eager_intro]
ghost fn eta_expanded_unit ()
  ensures eta_expanded ()
{ fold eta_expanded () }

[@@pulse_eager_intro]
ghost fn eta_expanded_erased (#t: Type0) (x: erased t)
  requires eta_expanded (reveal x)
  ensures eta_expanded x
{ unfold eta_expanded (reveal x); fold eta_expanded x }

[@@pulse_eager_intro]
ghost fn eta_expanded_pair (#t #s: Type0) (x: t) (y: s)
  requires eta_expanded x
  requires eta_expanded y
  ensures eta_expanded (x, y)
{ unfold eta_expanded x; unfold eta_expanded y; fold eta_expanded (x, y) }

assume val call (x: R.ref int) (w: erased (unit & int))
  : stt unit (eta_expanded w ** (let (_, v) = reveal w in R.pts_to x v))
             (fun _ -> R.pts_to x (snd (reveal w)))

assume val havoc (n: int) (x: R.ref int) :
  stt unit (R.pts_to x 0) (fun _ -> exists* v. R.pts_to x v)

fn test (a: R.ref int)
  requires R.pts_to a 0
  ensures exists* v. R.pts_to a v
{
  let mut n = 0;
  let n1 = !n;
  havoc n1 a;
  call a _;
}

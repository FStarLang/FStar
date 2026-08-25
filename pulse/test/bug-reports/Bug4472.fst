module Bug4472
#lang-pulse

(* Issue #4472: a fold-direction [rewrite], i.e. one whose right-hand side is a
   [pulse_unfold] typeclass-instance projection, must discharge just like the
   unfold-direction one.  The projection is stuck until its scrutinee (the
   instance) is unfolded, which is what makes the two sides of the equality
   asymmetric. *)

open Pulse
include Pulse.Lib.Reference
open FStar.Tactics.Typeclasses { noinst }

let maybe_pts_to (#a: Type u#a) ([@@@mkey] r:ref a) (#f:perm) (x:option a) : slprop =
  if is_null r then pure (x == None)
  else exists* v. (r |-> Frac f v) ** pure (x == Some v)

(* The attributes below mirror Pulse's own has_pts_to / ( |-> ) / pts_to_frac. *)
[@@FStar.Tactics.Typeclasses.fundeps [1]; pulse_unfold]
class has_my (p r : Type) = {
  [@@@pulse_unfold]
  my : p -> (#[full_default()] f : perm) -> r -> slprop;
}

[@@pulse_unfold]
let ( |--> ) #p #r {| has_my p r |} = my #p #r

[@@pulse_unfold; noinst]
instance my_frac (p a : Type) (d : has_my p a) : has_my p (frac a) = {
  my = (fun p #f' (Frac f v) -> d.my p #(f' *. f) v);
}

[@@pulse_unfold]
instance my_base (a:Type) : has_my (ref a) (option a) = {
  my = (fun r #f v -> maybe_pts_to r #f v);
}

(* Unfolding the instance. *)
ghost
fn elim_null u#a (#a: Type u#a) (r:ref a) #p (#x:option a)
requires r |--> Frac p x
requires pure (is_null r)
ensures pure (x == None)
{
  rewrite (r |--> Frac p x) as maybe_pts_to r #p x;
  unfold maybe_pts_to;
  rewrite each (is_null r) as true;
}

(* Folding into the instance. *)
ghost
fn intro_null u#a (#a: Type u#a) (r:ref a) #p
requires pure (is_null r)
ensures r |--> Frac p None
{
  rewrite (pure (None #a == None #a)) as (maybe_pts_to r #p None);
  rewrite (maybe_pts_to r #p None) as (r |--> Frac p None);
}

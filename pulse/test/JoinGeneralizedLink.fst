module JoinGeneralizedLink
#lang-pulse
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference

(* A branch that stores an unspecified encoding [c] of [x], known only
   through a pure fact, joined with a branch that leaves the cell alone.
   Generalizing the cell's value over a fresh binder must keep, for each
   branch, what that binder stands for: the encoded value and its fact in
   one, the old value in the other. *)

assume val repr : int -> int -> prop
assume val ok : int -> prop

assume val ok_enc (x c:int)
: Lemma (requires repr x c /\ ok x) (ensures ok (c + 1)) [SMTPat (repr x c)]

assume val store (r:R.ref int) (x:int) (#v:erased int)
: stt unit (R.pts_to r v) (fun _ -> exists* c. R.pts_to r (c + 1) ** pure (repr x c))

fn store_if (b:bool) (r:R.ref int) (x:int) (#v:erased int)
requires R.pts_to r v ** pure (ok v /\ ok x)
ensures exists* w. R.pts_to r w ** pure (ok w)
{
  if b { store r x } else { () };
  ()
}

(* The same, with the branches swapped. *)
fn store_unless (b:bool) (r:R.ref int) (x:int) (#v:erased int)
requires R.pts_to r v ** pure (ok v /\ ok x)
ensures exists* w. R.pts_to r w ** pure (ok w)
{
  if b { () } else { store r x };
  ()
}

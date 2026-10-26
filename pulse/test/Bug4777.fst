module Bug4777
#lang-pulse

(* https://github.com/FStarLang/FStar/issues/4777

   Initialized local arrays used to require [exists* v. pts_to arr v] at the
   end of their scope, so they could not be released after a function that
   leaves them uninitialized. *)

open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array
module U64 = FStar.UInt64

assume val forget (a: A.array U64.t) (#s: erased (Seq.seq U64.t))
  : stt unit (A.pts_to a s) (fun _ -> A.pts_to_uninit a (Seq.length s))

fn initialized_local () returns r: U64.t
{
  let mut a = [| 0uL; 4sz |];
  let r = a.(0sz);
  forget a;
  r
}

(* Ending with [pts_to] still works, for both kinds of locals. *)
fn initialized_local_pts_to () returns r: U64.t
  ensures pure (r == 3uL)
{
  let mut a = [| 0uL; 4sz |];
  a.(1sz) <- 3uL;
  a.(1sz)
}

fn uninit_local_pts_to () returns r: U64.t
{
  let mut a : A.array U64.t = [| 2sz |];
  A.mask_write a 0sz 1uL;
  A.mask_write a 1sz 1uL;
  A.from_mask a;
  a.(0sz)
}

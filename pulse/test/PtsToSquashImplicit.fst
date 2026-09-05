(* Regression test: resolving a typeclass constraint whose index mentions the
   result of a partial operation, so the goal carries an unsolved
   [squash]-typed implicit for the operation's precondition.
   Derived from a Kuiper regression (Kuiper.Kernel.Stencil). *)
module PtsToSquashImplicit
#lang-pulse

open Pulse.Lib.Pervasives
module SZ = FStar.SizeT

assume val myarr : SZ.t -> Type0
assume val chest : SZ.t -> Type0
assume val myarr_pts_to (#n:SZ.t) (a : myarr n) (p:perm) (c : chest n) : slprop

instance has_pts_to_myarr (n:SZ.t) : has_pts_to (myarr n) (chest n) = {
  pts_to = (fun a #p c -> myarr_pts_to a p c);
}

let two : SZ.t = 2sz

let kpre
    (#rows : SZ.t)
    (#_ : squash (SZ.fits (SZ.v rows + SZ.v two)))
    (g : myarr (SZ.add rows two))
    (e : chest (SZ.add rows two))
  : slprop
  = g |-> e

let kpre_frac
    (#rows : SZ.t)
    (#_ : squash (SZ.fits (SZ.v rows + SZ.v two)))
    (g : myarr (SZ.add rows two))
    (e : chest (SZ.add rows two))
  : slprop
  = g |-> Frac 0.5R e

module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Actions
#lang-pulse

(**
Composition patterns shared by the queue's two linearization proofs.

A client AU and an implementation invariant have different lifetimes. We
open the AU explicitly, execute one ordinary atomic operation that opens
the queue invariant lexically, restore that invariant, and only then execute
the AU's closing update. `delay` packages ownership needed for this last
step instead of trying to escape a lexical block with its invariant open.

This uses Iris-inspired update wands as first-class ghost continuations.
The footprint-disjointness check is essential: the implementation step must
not reopen a client invariant that the AU already holds. These helpers
still use run_closed and so expose all_inames to their outer caller.
`from_owned` is the simpler sequential-client specialization with no client
invariant or opening credit; it is not a generic concurrent sharing rule.
*)

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module U = Pulse.Lib.LogicalAtomicity.Update

(** Capture pre and its inner-to-empty cleanup in a suspended update. No
cleanup runs here; the lexical implementation invariant can be restored
before with_update eliminates this package. This adds no physical step. *)
ghost fn delay (inner:inames) (pre post:slprop)
  (f:unit -> M.gaction unit inner emp_inames pre (fun _ -> post))
  requires pre
  ensures U.fupd inner emp_inames post
{
  slprop_equivs ();
  U.intro_wand inner emp_inames emp post pre
    (fun _ -> M.sub_ghost (pre ** emp) (fun _ -> post) (f ()));
  fold U.fupd inner emp_inames post;
}

(** Open one AU, frame extra across it, run one footprint-disjoint atomic
step, then execute its delayed closing update while preserving keep.
The step must return its implementation invariant already closed.
AU credits are supplied by the caller; any implementation-opening credit
belongs in extra and is accounted for separately. *)
val with_update (#s #a #r:Type0)
  (inner:inames) (footprint:inames { inner /! footprint }) (credits:nat)
  (alpha:s -> slprop) (beta phi:s -> a -> slprop)
  (extra keep:slprop) (post:r -> slprop)
  (step:unit -> stt_atomic r footprint
    (A.opened emp_inames inner alpha
      (A.atomic_update emp_inames inner credits alpha beta phi) beta phi ** extra)
    (fun r -> U.fupd inner emp_inames (post r) ** keep))
  : stt_atomic r all_inames
      ((A.atomic_update emp_inames inner credits alpha beta phi ** later_credit credits) ** extra)
      (fun r -> post r ** keep)
let with_update #s #a #r inner footprint credits alpha beta phi extra keep post step
  : stt_atomic r all_inames
      ((A.atomic_update emp_inames inner credits alpha beta phi ** later_credit credits) ** extra)
      (fun r -> post r ** keep) =
  M.run_closed (
    M.bind (M.ghost_to_action (M.frame_ghost extra
      (A.open_update emp_inames inner credits alpha beta phi)))
      (fun _ ->
        M.bind (M.lift_atomic inner (step ()))
          (fun r ->
            M.finish_ghost r (fun r -> post r ** keep)
              (M.frame_ghost keep (U.elim_update inner emp_inames (post r))))))

(** Empty-footprint identity used as the owned-state abort/commit callback. *)
private ghost fn identity (p:slprop) () preserves p {}

(** Turn private alpha x into a zero-credit AU whose success returns beta
at that original x. Abort returns the same privately owned alpha; there is
no intervening client-invariant state change to hide existentially. *)
ghost fn from_owned (#s #a:Type0) (alpha:s -> slprop) (beta:s -> a -> slprop) (x:s)
  requires alpha x
  ensures A.atomic_update emp_inames emp_inames 0 alpha beta (fun _ y -> beta x y)
{
  // The retry invariant is alpha x itself; both closing branches are
  // identities on their respective resources at the empty mask.
  ghost fn step ()
    requires alpha x ** later_credit 0
    ensures A.opened emp_inames emp_inames alpha (alpha x) beta (fun _ y -> beta x y)
  {
    drop_ (later_credit 0);
    slprop_equivs ();
    A.intro_closing emp_inames emp_inames alpha (alpha x) beta (fun _ y -> beta x y) x emp
      (fun _ -> M.sub_ghost (emp ** alpha x) (fun _ -> alpha x)
        (M.lift_ghost emp_inames (identity (alpha x) ())))
      (fun y -> M.sub_ghost (emp ** beta x y) (fun _ -> beta x y)
        (M.lift_ghost emp_inames (identity (beta x y) ())));
    fold A.opened emp_inames emp_inames alpha (alpha x) beta (fun _ y -> beta x y);
  };
  A.intro emp_inames emp_inames 0 alpha beta (fun _ y -> beta x y) (alpha x)
    (fun _ -> M.lift_ghost emp_inames (step ()));
}

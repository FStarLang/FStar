module Pulse.Lib.LogicalAtomicity.Invariant
friend Pulse.Lib.Inv
#lang-pulse

(**
Locality-preserving bridge from core to ordinary invariants.

Pulse.Lib.Inv hides a core invariant at a storage locality together with
transport functions to/from the caller's locality. We unpack precisely that
representation, use Masks to move its core body, and restore the wrapper.
We must not identify `somewhere (later p)` with plain p: both locality
transport and later-credit elimination are real proof obligations.

Friend access exposes an existing representation, not a new invariant
axiom. The public interface deliberately hides these implementation views.
*)

open Pulse.Lib.Pervasives
module I = Pulse.Lib.Inv
module C = Pulse.Lib.Core.Inv
module M = Pulse.Lib.LogicalAtomicity.Masks

(** Erased witnesses for the caller/storage localities and reversible ghost
transport. They describe the original invariant wrapper's representation. *)
[@@erasable]
noeq type view (p:slprop) = {
  here:loc_id;
  there:loc_id;
  forward:unit -> stt_ghost unit emp_inames (on here p) (fun _ -> on there p);
  backward:unit -> stt_ghost unit emp_inames (on there p) (fun _ -> on here p);
}

(** Caller-locality ownership and the tag identifying the transport pair;
these resources must survive opening of the underlying core invariant. *)
let rest p (v:view p) =
  loc v.here ** I.move_tag v.here v.there p v.forward v.backward

(** Unpacked ordinary invariant: core handle plus its locality wrapper. *)
let held i p (v:view p) =
  C.inv i (on v.there p) ** rest p v

(** Expose a view without opening the invariant or consuming a later credit. *)
private ghost fn unpack i p
  requires inv i p
  returns v:view p
  ensures held i p v
{
  unfold inv i p;
  with l l' f g. _;
  let v = { here=l; there=l'; forward=f; backward=g };
  drop_ (I.move_tag l l' p f g);
  rewrite each l as v.here;
  rewrite each l' as v.there;
  fold I.move_tag v.here v.there p v.forward v.backward;
  fold rest p v;
  fold held i p v;
  v
}

(** Hide an unchanged view back behind the ordinary invariant predicate. *)
private ghost fn repack i p (v:view p)
  requires held i p v
  ensures inv i p
{
  unfold held i p v;
  unfold rest p v;
  fold inv i p;
}

(** Eliminate one later, transport the body back to the caller, and rebuild
the public handle while leaving p available. This is the credit-consuming
part of opening; it does not erase the locality requirement by fiat. *)
private ghost fn expose i p (v:view p)
  requires held i p v
  requires C.somewhere (later (on v.there p)) ** later_credit 1
  ensures inv i p ** p
{
  unfold held i p v;
  unfold rest p v;
  unfold C.somewhere (later (on v.there p));
  with l. _;
  on_on_eq l v.there (later p);
  on_later_eq v.there p;
  rewrite on l (later (on v.there p)) as later (on v.there p);
  later_elim (on v.there p);
  let backward = v.backward;
  backward ();
  on_elim p;
  fold inv i p;
}

(** Transport p into storage, introduce later, and package the localized
body required by core closing. No credit is needed to introduce later. *)
private ghost fn conceal i p (v:view p)
  requires held i p v ** p
  ensures held i p v ** C.somewhere (later (on v.there p))
{
  unfold held i p v;
  unfold rest p v;
  on_intro p;
  let forward = v.forward;
  forward ();
  later_intro (on v.there p);
  on_intro (later (on v.there p));
  fold C.somewhere (later (on v.there p));
  fold rest p v;
  fold held i p v;
}

(** Unpack, open the core handle with the wrapper framed, then expose p.
The output mask accounts for the still-outstanding invariant body. *)
let open_inv mask i p
  : M.gaction unit mask (add_inv mask i)
      (inv i p ** later_credit 1) (fun _ -> inv i p ** p) =
  slprop_equivs ();
  M.bind_ghost #(view p) #unit
    #mask #mask #(add_inv mask i)
    #_ #_ #(fun _ -> inv i p ** p)
    (M.lift_ghost mask (frame_ghost (later_credit 1) (unpack i p)))
    (fun v ->
      assert (held i p v == C.inv i (on v.there p) ** rest p v)
        by (FStar.Tactics.V2.trefl ());
      M.bind_ghost #unit #unit
        #mask #(add_inv mask i) #(add_inv mask i)
        #_ #_ #(fun _ -> inv i p ** p)
        (M.sub_ghost (held i p v ** later_credit 1)
          (fun _ -> held i p v ** C.somewhere (later (on v.there p)) ** later_credit 1)
          (M.frame_ghost (rest p v ** later_credit 1) (M.open_invariant mask i (on v.there p))))
        (fun _ -> M.lift_ghost (add_inv mask i) (expose i p v)))

(** Conceal p, restore the core invariant resource, and repack the wrapper.
This removes only i, so unrelated open invariants may remain outstanding. *)
let close_inv mask i p
  : M.gaction unit (add_inv mask i) mask
      (inv i p ** p) (fun _ -> inv i p) =
  slprop_equivs ();
  M.bind_ghost #(view p) #unit
    #(add_inv mask i) #(add_inv mask i) #mask #_ #_ #(fun _ -> inv i p)
    (M.lift_ghost (add_inv mask i) (frame_ghost p (unpack i p)))
    (fun v ->
      assert (held i p v == C.inv i (on v.there p) ** rest p v)
        by (FStar.Tactics.V2.trefl ());
      M.bind_ghost (M.lift_ghost (add_inv mask i) (conceal i p v))
        (fun _ ->
          M.bind_ghost #unit #unit
            #(add_inv mask i) #mask #mask #_ #_ #(fun _ -> inv i p)
            (M.sub_ghost (held i p v ** C.somewhere (later (on v.there p)))
              (fun _ -> held i p v)
              (M.frame_ghost (rest p v) (M.close_invariant mask i (on v.there p))))
            (fun _ -> M.lift_ghost mask (repack i p v))))

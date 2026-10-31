module Pulse.Lib.LogicalAtomicity.Triple
#lang-pulse

(**
Proof of the invariant-backed AU constructor.

The hidden retry state is `inv i (payload alpha residual) ** extra`.
Opening lends alpha to the implementation and keeps residual plus extra in
one additive closing choice. Abort puts the old payload back; commit runs
the client's ghost continuation and puts its replacement payload back.
Both branches close i before returning to the outer mask.

The HoCAP-like callback is entirely ghost code and cannot perform another
observable operation at the linearization point. The executable operation
must separately prove its alpha-to-beta step, as the examples demonstrate.
*)

open Pulse.Lib.Pervasives
module A = Pulse.Lib.LogicalAtomicity.Atomic
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant

(** Reassemble the old invariant payload without using the captured extra;
the latter remains available for a later retry. *)
private ghost fn prepare_abort (#a:Type0) i (alpha residual:a -> slprop) extra x
  requires (inv i (payload alpha residual) ** extra ** residual x) ** alpha x
  ensures (inv i (payload alpha residual) ** payload alpha residual) ** extra
{
  fold payload alpha residual;
}

(** Run client ghost code against the operation's beta. It must rebuild the
entire invariant payload and establish phi, not merely update a ghost value. *)
private ghost fn prepare_commit (#a #b:Type0) i
  (alpha residual:a -> slprop) (beta phi:a -> b -> slprop) extra
  (finish:(x:a -> y:b -> unit ->
    stt_ghost unit emp_inames (extra ** residual x ** beta x y)
      (fun _ -> payload alpha residual ** phi x y)))
  x y
  requires (inv i (payload alpha residual) ** extra ** residual x) ** beta x y
  ensures (inv i (payload alpha residual) ** payload alpha residual) ** phi x y
{
  let finish = finish x y;
  finish ();
}

(** Discard the now-unneeded persistent handle after successful closing.
The invariant itself is not deallocated; q is the client's returned result. *)
private ghost fn forget_inv i p q
  requires inv i p ** q
  ensures q
{
  drop_ (inv i p);
}

(** Capture residual and extra once in an additive abort/commit choice.
Frame extra across abort closing and phi across commit closing. *)
private ghost fn make_closing (#a #b:Type0)
  (outer:inames) (i:iname { not (mem_inv outer i) })
  (alpha residual:a -> slprop) (beta phi:a -> b -> slprop) extra
  (finish:(x:a -> y:b -> unit ->
    stt_ghost unit emp_inames (extra ** residual x ** beta x y)
      (fun _ -> payload alpha residual ** phi x y)))
  requires inv i (payload alpha residual) ** payload alpha residual ** extra
  ensures A.opened outer (add_inv outer i) alpha
    (inv i (payload alpha residual) ** extra) beta phi
{
  unfold payload alpha residual;
  with x. _;
  slprop_equivs ();
  A.intro_closing outer (add_inv outer i) alpha
    (inv i (payload alpha residual) ** extra) beta phi x
    (inv i (payload alpha residual) ** extra ** residual x)
    (fun _ ->
      M.bind_ghost
        (M.lift_ghost (add_inv outer i) (prepare_abort i alpha residual extra x))
        (fun _ -> M.frame_ghost extra (I.close_inv outer i (payload alpha residual))))
    (fun y ->
      M.bind_ghost
        (M.lift_ghost (add_inv outer i) (prepare_commit i alpha residual beta phi extra finish x y))
        (fun _ ->
          M.bind_ghost (M.frame_ghost (phi x y) (I.close_inv outer i (payload alpha residual)))
            (fun _ -> M.lift_ghost outer (forget_inv i (payload alpha residual) (phi x y)))));
  fold A.opened outer (add_inv outer i) alpha
    (inv i (payload alpha residual) ** extra) beta phi;
}

(** Instantiate Atomic.intro with the invariant-backed retry state. Its step
opens i and installs make_closing; Atomic wraps the abort result back into
an AU, allowing fresh-credit retries without duplicating extra. *)
ghost fn from_invariant (#a #b:Type0)
  (outer:inames) (i:iname { not (mem_inv outer i) })
  (alpha residual:a -> slprop) (beta phi:a -> b -> slprop) (extra:slprop)
  (finish:(x:a -> y:b -> unit ->
    stt_ghost unit emp_inames (extra ** residual x ** beta x y)
      (fun _ -> payload alpha residual ** phi x y)))
  requires inv i (payload alpha residual) ** extra
  ensures A.atomic_update outer (add_inv outer i) 1 alpha beta phi
{
  slprop_equivs ();
  A.intro outer (add_inv outer i) 1 alpha beta phi
    (inv i (payload alpha residual) ** extra)
    (fun _ ->
      M.bind_ghost
        (M.sub_ghost ((inv i (payload alpha residual) ** extra) ** later_credit 1)
          (fun _ -> inv i (payload alpha residual) ** payload alpha residual ** extra)
          (M.frame_ghost extra (I.open_inv outer i (payload alpha residual))))
        (fun _ -> M.lift_ghost (add_inv outer i)
          (make_closing outer i alpha residual beta phi extra finish)));
}

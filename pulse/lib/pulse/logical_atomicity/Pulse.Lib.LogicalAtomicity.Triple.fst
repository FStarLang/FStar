module Pulse.Lib.LogicalAtomicity.Triple
#lang-pulse

open Pulse.Lib.Pervasives
module A = Pulse.Lib.LogicalAtomicity.Atomic
module M = Pulse.Lib.LogicalAtomicity.Masks
module I = Pulse.Lib.LogicalAtomicity.Invariant

private ghost fn prepare_abort (#a:Type0) i (alpha residual:a -> slprop) extra x
  requires (inv i (payload alpha residual) ** extra ** residual x) ** alpha x
  ensures (inv i (payload alpha residual) ** payload alpha residual) ** extra
{
  fold payload alpha residual;
}

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

private ghost fn forget_inv i p q
  requires inv i p ** q
  ensures q
{
  drop_ (inv i p);
}

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

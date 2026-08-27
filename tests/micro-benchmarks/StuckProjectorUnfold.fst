module StuckProjectorUnfold

open FStar.Tactics.V2

(* Issue #4472: projectors are declaration-only, so there is no definition of
   the projector itself for the core typechecker to unfold when it compares a
   projection against something else.  Progress on such a stuck projection can
   only be made by unfolding inside its scrutinee, which is what the projector's
   definition used to expand to.  Without that, the two terms below are only
   related in the direction in which [opaque_prop] can be unfolded. *)

noeq type wrap (a:Type) = | Wrap : a -> wrap a

assume val opaque_prop (r:int) (f:int) : Type0

class has_my (r : Type) = { my : r -> int -> Type0 }

instance my_base : has_my (wrap int) = { my = (fun (Wrap r) f -> opaque_prop r f) }

let test (r:int) (f:int) : unit =
  assert True by (
    let t0 = quote (opaque_prop r f) in
    let t1 = quote (my_base.my (Wrap r) f) in
    let e = cur_env () in
    let res, _ = t_check_equiv false true e t0 t1 in
    if None? res then fail "not equivalent";
    let res, _ = t_check_equiv false true e t1 t0 in
    if None? res then fail "not equivalent (reversed)";
    trivial ()
  )

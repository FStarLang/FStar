module Pulse.Lib.LogicalAtomicity.Example.Read
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module T = Pulse.Lib.LogicalAtomicity.Triple
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module U32 = FStar.UInt32

let alpha r (n:U32.t) = B.pts_to r n
let beta r (n:U32.t) (v:U32.t) = alpha r n ** pure (v == n)
let update r inner phi =
  A.atomic_update emp_inames inner 1 (alpha r) (beta r) (fun n _ -> phi n)
let opened r inner phi =
  A.opened emp_inames inner (alpha r) (update r inner phi) (beta r) (fun n _ -> phi n)
let closing r inner phi n =
  A.closing emp_inames inner (alpha r) (update r inner phi) (beta r) (fun n _ -> phi n) n

atomic fn read_opened (r:B.box U32.t) inner phi
  requires opened r inner phi
  returns v:U32.t
  ensures closing r inner phi v ** beta r v v
{
  unfold opened r inner phi;
  unfold A.opened;
  with n. _;
  unfold alpha r n;
  let v = read_atomic_box r;
  rewrite each n as v;
  fold alpha r v;
  fold beta r v v;
  fold closing r inner phi v;
  v
}

val read_attempt (r:B.box U32.t) (inner:inames) (phi:U32.t -> slprop)
  : stt_atomic U32.t all_inames (update r inner phi ** later_credit 1) (fun v -> phi v)
let read_attempt r inner phi
  : stt_atomic U32.t all_inames (update r inner phi ** later_credit 1) (fun v -> phi v) =
  M.run_closed (
    M.bind (M.ghost_to_action (A.open_update emp_inames inner 1 (alpha r) (beta r) (fun n _ -> phi n)))
      (fun _ ->
        M.bind (M.lift_atomic inner (read_opened r inner phi))
          (fun v ->
            M.finish_ghost v (fun v -> phi v)
              (A.commit emp_inames inner (alpha r) (update r inner phi) (beta r) (fun n _ -> phi n) v v))))

fn read (r:B.box U32.t) inner phi
  requires update r inner phi
  returns v:U32.t
  ensures phi v
{
  later_credit_buy 1;
  let v = read_attempt r inner phi;
  v
}

let residual g (n:U32.t) = G.pts_to g #0.5R n
let observed g n = G.pts_to g #0.5R 37ul ** pure (n == 37ul)

// Unlike fetch_add, the linearization point preserves the abstract state.
fn client ()
  returns result:(B.box U32.t & U32.t)
  ensures exists* i g.
    inv i (T.payload (alpha (fst result)) (residual g)) **
    G.pts_to g #0.5R 37ul ** pure (snd result == 37ul)
{
  let r = B.alloc 37ul;
  let g = G.alloc 37ul;
  G.share g;
  fold alpha r 37ul;
  fold residual g 37ul;
  fold T.payload (alpha r) (residual g);
  let i = new_invariant (T.payload (alpha r) (residual g));

  ghost fn finish (n:U32.t) (v:U32.t) ()
    requires G.pts_to g #0.5R 37ul ** residual g n ** beta r n v
    ensures T.payload (alpha r) (residual g) ** observed g n
  {
    unfold residual g n;
    G.pts_to_injective_eq g;
    rewrite each n as 37ul;
    unfold beta r 37ul v;
    fold residual g 37ul;
    fold T.payload (alpha r) (residual g);
    fold observed g 37ul;
    rewrite observed g 37ul as observed g n;
  };

  T.from_invariant emp_inames i (alpha r) (residual g) (beta r) (fun n _ -> observed g n)
    (G.pts_to g #0.5R 37ul) finish;
  fold update r (add_inv emp_inames i) (observed g);
  let v = read r (add_inv emp_inames i) (observed g);
  unfold observed g v;
  (r, v)
}

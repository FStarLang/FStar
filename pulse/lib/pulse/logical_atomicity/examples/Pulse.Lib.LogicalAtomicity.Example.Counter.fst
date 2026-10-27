module Pulse.Lib.LogicalAtomicity.Example.Counter
#lang-pulse

open Pulse.Lib.Pervasives
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module T = Pulse.Lib.LogicalAtomicity.Triple
module B = Pulse.Lib.Box
module G = Pulse.Lib.GhostReference
module U32 = FStar.UInt32

let alpha (r:B.box U32.t) (n:U32.t) = B.pts_to r n
let beta (r:B.box U32.t) (n:U32.t) (_:unit) = alpha r (U32.add_mod n 1ul)
let update r inner credits (phi:U32.t -> slprop) =
  A.atomic_update emp_inames inner credits (alpha r) (beta r) (fun n _ -> phi n)
let opened r inner credits phi =
  A.opened emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n)
let closing r inner credits phi n =
  A.closing emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n) n

atomic fn read_opened r inner credits phi
  preserves opened r inner credits phi
  returns v:U32.t
{
  unfold opened r inner credits phi;
  unfold A.opened;
  with n. _;
  unfold alpha r n;
  let v = read_atomic_box r;
  fold alpha r n;
  fold A.opened emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n);
  fold opened r inner credits phi;
  v
}

val read_attempt (r:B.box U32.t) (inner:inames) (credits:nat) (phi:U32.t -> slprop)
  : stt_atomic U32.t all_inames (update r inner credits phi ** later_credit credits)
      (fun _ -> update r inner credits phi)
let read_attempt r inner credits phi
  : stt_atomic U32.t all_inames (update r inner credits phi ** later_credit credits)
      (fun _ -> update r inner credits phi) =
  M.run_closed (
    M.bind (M.ghost_to_action (A.open_update emp_inames inner credits (alpha r) (beta r) (fun n _ -> phi n)))
      (fun _ ->
        M.bind (M.lift_atomic inner (read_opened r inner credits phi))
          (fun v ->
            M.finish_ghost v (fun _ -> update r inner credits phi)
              (A.abort_opened emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n)))))

atomic fn cas_opened r inner credits phi (expected:U32.t)
  requires opened r inner credits phi
  returns ok:bool
  ensures (if ok then closing r inner credits phi expected ** beta r expected ()
          else opened r inner credits phi)
{
  unfold opened r inner credits phi;
  unfold A.opened;
  with n. _;
  unfold alpha r n;
  let ok = cas_box r expected (U32.add_mod expected 1ul);
  if ok {
    elim_cond_true _ _ _;
    rewrite each n as expected;
    fold alpha r (U32.add_mod expected 1ul);
    fold beta r expected ();
    fold closing r inner credits phi expected;
    true
  } else {
    elim_cond_false _ _ _;
    fold alpha r n;
    fold A.opened emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n);
    fold opened r inner credits phi;
    false
  }
}

val try_attempt (r:B.box U32.t) (inner:inames) (credits:nat) (phi:U32.t -> slprop) (expected:U32.t)
  : stt_atomic bool all_inames (update r inner credits phi ** later_credit credits)
      (fun ok -> if ok then phi expected else update r inner credits phi)
let try_attempt r inner credits phi expected
  : stt_atomic bool all_inames (update r inner credits phi ** later_credit credits)
      (fun ok -> if ok then phi expected else update r inner credits phi) =
  M.run_closed (
    M.bind (M.ghost_to_action (A.open_update emp_inames inner credits (alpha r) (beta r) (fun n _ -> phi n)))
      (fun _ ->
        M.bind (M.lift_atomic inner (cas_opened r inner credits phi expected))
          (fun ok ->
            if ok then
              M.finish_ghost true (fun ok -> if ok then phi expected else update r inner credits phi)
                (A.commit emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n) expected ())
            else
              M.finish_ghost false (fun ok -> if ok then phi expected else update r inner credits phi)
                (A.abort_opened emp_inames inner (alpha r) (update r inner credits phi) (beta r) (fun n _ -> phi n)))))

divergent fn rec fetch_add (r:B.box U32.t) (inner:inames) (credits:nat) (phi:U32.t -> slprop)
  requires update r inner credits phi
  returns old:U32.t
  ensures phi old
{
  later_credit_buy credits;
  let expected = read_attempt r inner credits phi;
  later_credit_buy credits;
  let ok = try_attempt r inner credits phi expected;
  if ok {
    expected
  } else {
    fetch_add r inner credits phi
  }
}

let residual (g:G.ref U32.t) (n:U32.t) = G.pts_to g #0.5R n
let client_post g n = G.pts_to g #0.5R 1ul ** pure (n == 0ul)

divergent fn client_once ()
  returns result:(B.box U32.t & U32.t)
  ensures exists* i g.
    inv i (T.payload (alpha (fst result)) (residual g)) **
    G.pts_to g #0.5R 1ul ** pure (snd result == 0ul)
{
  let r = B.alloc 0ul;
  let g = G.alloc 0ul;
  G.share g;
  fold alpha r 0ul;
  fold residual g 0ul;
  fold T.payload (alpha r) (residual g);
  let i = new_invariant (T.payload (alpha r) (residual g));

  ghost fn finish (n:U32.t) (_:unit) ()
    requires G.pts_to g #0.5R 0ul ** residual g n ** beta r n ()
    ensures T.payload (alpha r) (residual g) ** client_post g n
  {
    unfold residual g n;
    G.pts_to_injective_eq g;
    rewrite each n as 0ul;
    G.gather g;
    G.write g 1ul;
    G.share g;
    unfold beta r 0ul ();
    assert pure (U32.add_mod 0ul 1ul == 1ul);
    rewrite alpha r (U32.add_mod 0ul 1ul) as alpha r 1ul;
    fold residual g 1ul;
    fold T.payload (alpha r) (residual g);
    fold client_post g 0ul;
    rewrite client_post g 0ul as client_post g n;
  };

  T.from_invariant emp_inames i (alpha r) (residual g) (beta r) (fun n _ -> client_post g n)
    (G.pts_to g #0.5R 0ul) finish;
  fold update r (add_inv emp_inames i) 1 (client_post g);
  let old = fetch_add r (add_inv emp_inames i) 1 (client_post g);
  unfold client_post g old;
  (r, old)
}

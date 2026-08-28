module GhostProjectionUnfold

open FStar.Tactics.V2

(* Issue #4498: making progress on a stuck projection by unfolding inside its
   scrutinee must not produce a term that the core typechecker rejects.

   Unfolding [mk] below beta-reduces to its body under the [Tot] ascription that
   comes from the annotation of its definition; since the argument here is
   ghost, that ascription no longer holds and core checking of the unfolded term
   fails with "Expected a Total computation, but got Ghost".  The unfolding is
   useless anyway: the scrutinee of the match is a variable, so the projection
   stays stuck and the relation is decided by the SMT solver, exactly as it is
   without unfolding at all. *)

noeq type t = | A : nat -> t | B : nat -> t

let mk (x: t) : Tot (n: nat & nat) =
  match x with
  | A n -> (| n, n |)
  | B n -> (| n + 1, n |)

let test (v: Ghost.erased t) (h k: nat) (_: squash (mk v == (| h, k |))) : unit =
  assert True by (
    let e = cur_env () in
    let t0 = quote (dfst (mk (Ghost.reveal v))) in
    let t1 = quote h in
    let res, iss = t_check_equiv true true e t0 t1 in
    if None? res then (
      FStar.Stubs.Tactics.V2.Builtins.log_issues iss;
      fail "not equivalent"
    );
    trivial ()
  )

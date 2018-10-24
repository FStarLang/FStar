module Bug1571

open FStar.Tactics

type t : eqtype = | V of nat | W

let _ : (n: nat) -> squash (not (V n = W)) = _ by (
  let open FStar.Tactics in
  let n = intro () in
  norm [delta; iota; zeta; primops];
  trivial ();
  qed ()
)

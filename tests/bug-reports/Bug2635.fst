module Bug2635
open FStar.Tactics

//Original report by Benjamin Bonneau
let prove_False
      (pf : squash False)
      (_  : (pf0 : squash False) -> squash (eq2 #(squash False) pf ()))
  : squash False
  = pf

[@@expect_failure]
let absurd : squash False
  = _ by (// |- ?pf : squash l_False
          apply (`prove_False);
          let pf0 = intro () in
          // (pf0 : squash l_False) |- _ : ?pf == ()
          trefl ())

// Revised version, not depending on False by Aseem
assume
val p : Type0

let test (pr:squash p) (f: (unit -> squash (pr == ()))) : squash p = pr

[@@expect_failure]
let ugh () 
  : squash p
  = _ by (
      apply (`test);
      let _ = intro () in
      dump "A";
      trefl ()
    ) 


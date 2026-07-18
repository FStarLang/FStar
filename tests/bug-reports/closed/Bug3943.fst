module Bug3943

open FStar.Ghost
open FStar.Tactics.V2

// These two terms unify, no problem
#push-options "--no_smt"
let test0 (len : erased nat) =
  assert (
    hide #nat (reveal #nat len)
    ==
    len
  ) by trefl ()
#pop-options

// We also simplify the hide(reveal x) to make this trivial
#push-options "--no_smt"
let test1 (len : erased nat) =
  assert (
    hide #nat (reveal #nat len)
    ==
    len
  );
  ()
#pop-options

let natlt (x : erased nat) = y:nat{y < x}

// These functions also unify, no problem
#push-options "--no_smt"
let test2 (len : erased nat) =
  assert (
    (fun (x : natlt (hide #nat (reveal #nat len))) -> 1)
    ==
    (fun (x : natlt len) -> 1)
  ) by trefl ()
#pop-options

// And simplifications make this work without SMT too.
#push-options "--no_smt"
let test3 (len : erased nat) =
  assert (
    (fun (x : natlt (hide #nat (reveal #nat len))) -> 1)
    ==
    (fun (x : natlt len) -> 1)
  )
#pop-options

noeq
type foo (x : erased nat) = {
  ty : Type0;
}

#push-options "--no_smt"
let test4 (len : erased nat) (vw : foo len) =
  assert (
    (fun (x : (Mkfoo?.ty #(hide #nat (reveal #nat len)) vw)) -> 1)
    ==
    (fun (x : (Mkfoo?.ty #len vw)) -> 1)
  );
  ()
#pop-options

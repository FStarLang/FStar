module NegPrecondition

/// Expected to FAIL.  The precondition of `div` is not satisfied at the call
/// site, and the error must be reported *at the call site* (like a failing
/// refinement subtyping check), not as one opaque VC for the whole definition.

assume
val div : x:int -> y:int -> Pure int (requires (y =!= 0)) (ensures (fun r -> r * y == x))

[@@ expect_failure]
let bad (x:int) (y:int) : Pure int (requires True) (ensures (fun _ -> True)) =
  div x y

/// The postcondition must NOT leak into the result type: this assertion is not
/// provable from `nat` alone, and must fail.
assume val p : nat -> prop
assume val f : unit -> Pure nat (requires True) (ensures (fun n -> p n))

[@@ expect_failure]
let leaked () : Pure unit (requires True) (ensures (fun _ -> True)) =
  let g (n:nat) : Pure unit (requires True) (ensures (fun _ -> True)) = assert (p n) in
  g (f ())

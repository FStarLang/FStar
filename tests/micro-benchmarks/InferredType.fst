module InferredType

/// THE key regression test for this refactoring.
///
/// For `f : unit -> Pure nat (requires True) (ensures fun n -> p n)`, the
/// *inferred type* of `f ()` must remain `nat` -- NOT `n:nat{p n}`.
///
/// If the checker were to refine the result type with the postcondition, the
/// implicit type argument of `eq2` in `f () == 42` would be inferred as
/// `n:nat{p n}`, which is both surprising to the user and a source of
/// downstream unification failures.

assume val p : nat -> prop

assume val f : unit -> Pure nat (requires True) (ensures (fun n -> p n))

/// `eq2` must be instantiated at `nat`.
let eq_test () : Pure prop (requires True) (ensures (fun _ -> True)) =
  f () == 42

/// Same, through a polymorphic function that would otherwise get an
/// over-specific instantiation.
assume val id_poly : #a:Type -> a -> Tot a

let poly_test () : Pure nat (requires True) (ensures (fun _ -> True)) =
  id_poly (f ())

/// ...but the postcondition is still available as a hypothesis.
let post_available () : Pure unit (requires True) (ensures (fun _ -> True)) =
  let n = f () in
  assert (p n)

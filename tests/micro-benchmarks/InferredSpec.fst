module InferredSpec

/// An *unannotated* effectful function gets the default specification of its
/// effect.  It must not accumulate the pre- and postconditions of whatever its
/// body calls: that makes inferred signatures grow without bound, and it makes
/// phase 1 of two-phase type-checking (which drops specifications entirely)
/// disagree with phase 2.

assume val ensures_false : unit -> DIV unit (requires True) (ensures fun _ -> False)

/// [leaks] is unannotated, so its postcondition is [True], *not*
/// [ensures_false]'s.
let leaks () = ensures_false ()

/// Hence the postcondition is not available to callers of [leaks]...
[@@ expect_failure]
let post_does_not_leak () : DIV unit (requires True) (ensures fun _ -> False) =
  leaks ()

/// ...while it is still available to callers of [ensures_false] itself.
let post_of_annotated_is_kept () : DIV unit (requires True) (ensures fun _ -> False) =
  ensures_false ()

assume val requires_false : unit -> DIV unit (requires False) (ensures fun _ -> True)

/// Dually, the precondition of the body becomes a proof obligation right here
/// instead of being propagated into the inferred signature.
[@@ expect_failure]
let pre_does_not_leak () = requires_false ()

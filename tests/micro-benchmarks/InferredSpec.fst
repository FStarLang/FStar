module InferredSpec

/// A postcondition is a refinement of the result type, so it is part of the
/// type inferred for an unannotated effectful function and propagates to its
/// callers.  A precondition is a proof obligation, so it does not: it is
/// discharged where the call is written.

assume val ensures_false : unit -> DIV unit (requires True) (ensures fun _ -> False)

/// [propagates] is unannotated, so it gets [ensures_false]'s result type.
let propagates () = ensures_false ()

/// Hence the postcondition is available to callers of [propagates]...
let post_propagates () : DIV unit (requires True) (ensures fun _ -> False) =
  propagates ()

/// ...as it is to callers of [ensures_false] itself.
let post_of_annotated_is_kept () : DIV unit (requires True) (ensures fun _ -> False) =
  ensures_false ()

assume val requires_false : unit -> DIV unit (requires False) (ensures fun _ -> True)

/// Dually, the precondition of the body becomes a proof obligation right here
/// instead of being propagated into the inferred signature.
[@@ expect_failure]
let pre_does_not_leak () = requires_false ()

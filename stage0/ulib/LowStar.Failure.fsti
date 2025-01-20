module LowStar.Failure

/// This module exposes a single function for failure, which gets distinguished
/// treatment in KaRaMeL, is implemented in a header, correctly redirects to a
/// user-overridable KRML_HOST_EXIT macro (for situations where libc's exit(3)
/// does not apply), and does not require disabling C compiler warnings about
/// infinite recursion like C.Failure does.

val failwith: #a:Type -> Prims.string ->
  FStar.HyperStack.ST.Stack a
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> False))

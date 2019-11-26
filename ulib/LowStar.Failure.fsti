module LowStar.Failure

/// This module exposes a single function for failure, which gets distinguished
/// treatment in KreMLin, is implemented in a header (via a static inline
/// function), correctly redirects to a user-overridable KRML_HOST_EXIT macro
/// (for situations for libc's exit(2) does not apply), and does not require
/// disabling C compiler warnings about infinite recursion like C.Failure does.

val failwith: #a:Type -> Prims.string ->
  FStar.HyperStack.ST.Stack a
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> False))

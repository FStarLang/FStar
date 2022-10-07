module LowStar.Ignore

open FStar.HyperStack.ST

(** This module provides a distinguished `ignore` function; the function gets
    special treatment in KaRaMeL, which ensures that a call to `ignore e`
    results in KRML_IGNORE(e).

    By default, KRML_IGNORE(e) expands to (void)(e), but this behavior can be
    overridden (see include/krml/internal/target.h). *)

val ignore: #a:Type -> x:a -> Stack unit (fun _ -> True) (fun h0 _ h1 -> h0 == h1)

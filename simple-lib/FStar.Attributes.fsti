[@@"no_prelude"]
module FStar.Attributes

open Prims

/// Attributes understood by the type checker.  These are recognized by
/// their fully qualified name `FStar.Attributes.*` (see
/// `FStarC.Parser.Const.attr`), so they must be declared in this module.

val inline_let : unit
val plugin : int -> unit
val tcnorm : unit
val must_erase_for_extraction : unit
val expect_failure : list int -> unit
val expect_lax_failure : list int -> unit
val tcdecltime : unit
val unifier_hint_injective : unit
val no_auto_projectors : unit
val erasable : unit
val commute_nested_matches : unit
val noextract_to : string -> unit
val strict_on_arguments : list int -> unit
val no_subtyping : unit
val admit_termination : unit

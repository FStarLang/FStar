module FStarC.Syntax.Compress

open FStarC.Syntax.Syntax

(* Removes all delayed substitutions and resolved uvar nodes in a term.
if allow_uvars is false, it raises a hard error if an *unresolved* uvar
(term or universe) remains. Resolved uvars are replaced by their
solutions, as in compress. *)
val deep_compress (allow_uvars: bool) (allow_names: bool) (t:term) : term

(* Alias for deep_compress false true. i.e. allows names but not uvars,
useful to check that a potentially open term does not have any uvars. *)
val deep_compress_uvars (t:term) : term

(* Similar to `deep_compress false false t`, except instead of a hard error
   this returns None in case an unresolved uvar is found. *)
val deep_compress_if_no_uvars (t:term) : option term

val deep_compress_se (allow_uvars: bool) (allow_names: bool) (se:sigelt) : sigelt

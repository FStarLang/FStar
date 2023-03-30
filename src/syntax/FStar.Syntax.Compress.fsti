module FStar.Syntax.Compress

open FStar.Syntax.Syntax

(* Removes all delayed substitutions and resolved uvar nodes in a term.
if allow_uvars is false, it raises a hard error if an *unresolved* uvar
(term or universe) remains. Resolved uvars are replaced by their
solutions, as in compress. *)
val deep_compress (allow_uvars: bool) (t:term) : term

val deep_compress_se (allow_uvars: bool) (se:sigelt) : sigelt

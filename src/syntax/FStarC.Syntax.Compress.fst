module FStarC.Syntax.Compress
open FStarC

open FStarC
open FStarC
open FStarC.Util
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Syntax.Subst
open FStarC.Syntax.Visit

open FStarC.Class.Show

module List = FStarC.List
module Err = FStarC.Errors

(* This function really just checks for bad(tm) things happening, the
actual `compress` call is done by the visitor, so no need to repeat it
here. Morally, `deep_compress` is just `visit id` with some checks. *)
let compress1_t (allow_uvars: bool) (allow_names: bool) : term -> term =
  fun t ->
    let mk x = Syntax.mk x t.pos in
    match t.n with
    | Tm_uvar (uv, s) when not allow_uvars ->
      Err.raise_error0 Err.Error_UnexpectedUnresolvedUvar
        (format1 "Internal error: unexpected unresolved uvar in deep_compress: %s" (show uv))

    | Tm_name bv when not allow_names ->
      (* This currently happens, and often, but it should not! *)
      if Debug.any () then
        Errors.log_issue t Err.Warning_NameEscape (format1 "Tm_name %s in deep compress" (show bv));
      mk (Tm_name ({bv with sort = mk Tm_unknown}))

    (* The sorts are not needed. Delete them. *)
    | Tm_bvar bv -> mk (Tm_bvar ({bv with sort = mk Tm_unknown}))
    | Tm_name bv -> mk (Tm_name ({bv with sort = mk Tm_unknown}))

    | _ -> t

let compress1_u (allow_uvars:bool) (allow_names:bool) : universe -> universe =
  fun u ->
    match u with
    | U_name bv when not allow_names ->
      if Debug.any () then
        Errors.log_issue0 Err.Warning_NameEscape (format1 "U_name %s in deep compress" (show bv));
      u

    | U_unif uv when not allow_uvars ->
      Err.raise_error0 Err.Error_UnexpectedUnresolvedUvar
        (format1 "Internal error: unexpected unresolved (universe) uvar in deep_compress: %s" (show (Syntax.Unionfind.univ_uvar_id uv)))
    | _ -> u

(* deep_compress_*: eliminating all unification variables and delayed
substitutions in a sigelt. We traverse the entire syntactic structure
to evaluate the explicit lazy substitutions (Tm_delayed) and to replace
uvar nodes (Tm_uvar/U_unif) with their solutions.

The return value of this function should *never* contain a lambda. This
applies to every component of the term/sigelt: attributes, metadata, BV
sorts, universes, memoized free variables, substitutions, etc.

This is done to later dump the term/sigelt into a file (via OCaml's
output_value, for instance). This marshalling does not handle
closures[1] and we do not store the UF graph, so we cannot have any
lambdas and every uvar node that must be replaced by its solution (and
hence must have been resolved).

Eliminating the substitutions and resolving uvars is all done by the
`compress` call in the implementation of Visit.visit_tm, so this all
looks like a big identity function.

[1] OCaml's Marshal module can actually serialize closures, but this
makes .checked files more brittle, so we don't do it.
*)
let deep_compress (allow_uvars:bool) (allow_names: bool) (tm : term) : term =
  Err.with_ctx ("While deep-compressing a term") (fun () ->
    Visit.visit_term_univs true
      (compress1_t allow_uvars allow_names)
      (compress1_u allow_uvars allow_names)
      tm
  )

let deep_compress_uvars = deep_compress false true

let deep_compress_if_no_uvars (tm : term) : option term =
  Err.with_ctx ("While deep-compressing a term") (fun () ->
    try 
      Some (Visit.visit_term_univs true
              (compress1_t false true)
              (compress1_u false true)
              tm)
    with
    | Errors.Error (Err.Error_UnexpectedUnresolvedUvar, _, _, _) -> None
  )

let deep_compress_se (allow_uvars:bool) (allow_names:bool) (se : sigelt) : sigelt =
  Err.with_ctx (format1 "While deep-compressing %s" (Syntax.Print.sigelt_to_string_short se)) (fun () ->
    Visit.visit_sigelt true
      (compress1_t allow_uvars allow_names)
      (compress1_u allow_uvars allow_names)
      se
  )

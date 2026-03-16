module FStarC.TypeChecker.PatternInference

open FStarC.Effect
open FStarC.Syntax.Syntax

module Env = FStarC.TypeChecker.Env

(* Attempt to infer SMT patterns for a quantifier.
   If the term is a forall/exists application without user-supplied patterns,
   injects inferred patterns as Meta_pattern and returns the modified term.
   Otherwise returns the term unchanged.
   Guarded by --ext auto_patterns in the caller. *)
val maybe_infer_patterns : Env.env -> term -> ML term

(* Infer patterns at the Meta_pattern level.
   Called from TcTerm when processing Tm_meta{Meta_pattern(names, [])}.
   `names` are the quantifier-bound variables (as terms),
   `body` is the typechecked quantifier body.
   Returns inferred patterns (list of disjuncts) or empty list on failure. *)
val infer_patterns_for_meta : Env.env -> list term -> term -> ML (list (list arg))

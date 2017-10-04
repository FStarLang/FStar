/// ===========================
/// Pattern matching exceptions
/// ===========================

module PatternMatching.Exceptions

open FStar.Tactics
open PatternMatching.Types
open PatternMatching.Utils

/// Types of exceptions
/// ===================

noeq type match_exception =
| NameMismatch of qn * qn
| SimpleMismatch of pattern * term
| NonLinearMismatch of var * term * term
| UnsupportedTermInPattern of term

let string_of_match_exception = function
  | NameMismatch (qn1, qn2) ->
    "Match failure (name mismatch): expecting " ^ (string_of_qn qn1) ^ ", found " ^ (string_of_qn qn2)
  | SimpleMismatch (pat, tm) ->
    "Match failure (sort mismatch): expecting " ^ desc_of_pattern pat ^ ", got " ^ term_to_string tm
  | NonLinearMismatch (nm, t1, t2) ->
    "Match failure (nonlinear mismatch): variable " ^ nm ^
    " needs to match both " ^ (term_to_string t1) ^ " and " ^ (term_to_string t2)
  | UnsupportedTermInPattern tm ->
    "Match failure (unsupported term in pattern): " ^ term_to_string tm

/// Exception monad
/// ===============

noeq type match_res a =
| Success of a
| Failure of match_exception

let return #a (x: a) : match_res a =
  Success x

let bind (#a #b: Type)
         (f: match_res a)
         (g: a -> match_res b)
    : match_res b =
  match f with
  | Success aa -> g aa
  | Failure ex -> Failure ex

let raise #a (ex: match_exception) : match_res a =
  Failure ex

/// Liftings
/// ========

let lift_exn_tac #a #b (f: a -> match_res b) (aa: a) : Tac b =
  match f aa with
  | Success bb -> bb
  | Failure ex -> Tactics.fail (string_of_match_exception ex) ()

let lift_exn_tactic #a #b (f: a -> match_res b) (aa: a) : tactic b =
  match f aa with
  | Success bb -> Tactics.return bb
  | Failure ex -> Tactics.fail (string_of_match_exception ex)

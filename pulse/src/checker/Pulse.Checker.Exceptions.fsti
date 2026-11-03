module Pulse.Checker.Exceptions

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
module T = FStar.Tactics.V2

(* Native exceptions are checked by lowering to ordinary stateful computations:

     stt[_div] (Rules.native_outcome exn a) pre (Rules.exit_post q r)

   Normal x transfers q x; Raised e transfers r e. Inside a function, Raised
   exits use lexical goto labels, including the cleanup obligations of scopes
   crossed by the jump. No exception AST remains in the checked result.

   The checker callback checks generated returns, matches, and raises using the
   same rules as source terms. Passing it explicitly avoids a module dependency
   cycle through Pulse.Checker. Helpers for building outcomes and post hints
   are private to the implementation. *)

// Recognize the reserved result-type spelling, not all types definitionally
// equal to outcome. Some (exn, a) means a call must be split into two exits;
// raw Rules.outcome remains ordinary data even inside an exception scope.
// The input is the result type obtained by computation readback. This is a
// syntactic recognizer, not a typechecking or normalization operation.
val outcome_types (ty:term) : Tot (option (term & term))

// Check a raise after the main checker has hoisted stateful payload evaluation.
// The nearest exception label determines the payload type; its destination
// contract plus crossed cleanup obligations must consume the owned context.
// With no visible destination (also at a cleanup boundary), require False.
val check_raise
  (g:env)
  (pre:term)
  (ph:post_hint_opt g)
  (name:ppname)
  (arg:term)
  (rng:range)
  : T.Tac (checker_result_t g pre ph)

// Check a function's exception scope or a try's protected body. normal carries
// the unwrapped result type/postcondition; exceptional is an exn -> slprop
// expression. The actual entry context is pre. Check body with a fresh lexical
// destination, then close it, yielding a native_outcome computation. ph applies
// to that outcome, not to the body's normal result. Payloads/results are Type0,
// and the ambient effect must be STT or STTDiv.
val check_scope
  (g:env)
  (pre:term)
  (ph:post_hint_opt g)
  (name:ppname)
  (normal:comp_st)
  (exceptional:term)
  (body:st_term)
  (rng:range)
  (check:check_t)
  : T.Tac (checker_result_t g pre ph)

// Split an already checked native call. The caller supplies its result r,
// payload/result types exn and a, and its outcome-indexed postcondition post.
// These must describe the SAME computation, after adding the caller's frame.
// post binds the outcome at index 0. Only Normal continues with an a; Raised
// propagates through check_raise. This must run even when no exception label
// is visible or the source discards the call result. ph applies to the
// unwrapped normal continuation, not to the intermediate outcome.
val unwrap
  (#g:env)
  (#pre:term)
  (ph:post_hint_opt g)
  (name:ppname)
  (r:checker_result_t g pre NoHint)
  (exn a post:term)
  (rng:range)
  (check:check_t)
  : T.Tac (checker_result_t g pre ph)

// Check a try using the explicit protected-body exceptional contract.
// normal constrains both protected normal completion and catch results.
// handler has one payload binder at index 0; desugaring has already supplied
// its ordered pattern match and unmatched-payload re-raise. It is checked
// OUTSIDE the protected body's exception label, so re-raises target the outer
// scope. The returned computation exposes the normal result, not an outcome.
val check_try
  (g:env)
  (pre:term)
  (ph:post_hint_opt g)
  (name:ppname)
  (normal:comp_st)
  (exceptional:term)
  (body handler:st_term)
  (rng:range)
  (check:check_t)
  : T.Tac (checker_result_t g pre ph)

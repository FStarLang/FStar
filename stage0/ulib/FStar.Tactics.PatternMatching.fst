(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
/// ==========================
///  Pattern-matching tactics
/// ==========================
///
/// :Author: Clément Pit-Claudel
/// :Contact: clement.pitclaudel@live.com
/// :Date: 2017-10-13

module FStar.Tactics.PatternMatching

open FStar.Tactics.V2

/// Contents
/// ========
///
///  1  Contents
///  2  Motivation
///  3  Some utility functions
///  4  Pattern types
///  5  Pattern matching exceptions
///    5.1  Types of exceptions
///    5.2  The exception monad
///    5.3  Liftings
///  6  Pattern interpretation
///  7  Pattern-matching problems
///    7.1  Definitions
///    7.2  Resolution
///  8  A DSL for pattern-matching
///    8.1  Pattern notations
///    8.2  Problem notations
///    8.3  Continuations
///  9  Putting it all together
/// 10  Examples
///   10.1  Simple examples
///   10.2  A real-life example
/// 11  Possible extensions
/// 12  Notes
///
/// Motivation
/// ==========
///
/// Suppose you have a goal of the form ``squash (a == b)``.  How do you capture
/// `a` and `b` for further inspection?
///
/// Here's a basic (but cumbersome!) implementation:

let fetch_eq_side () : Tac (term & term) =
  let g = cur_goal () in
  match inspect g with
  | Tv_App squash (g, _) ->
    (match inspect squash with
     | Tv_UInst squash _
     | Tv_FVar squash ->
       if fv_to_string squash = flatten_name squash_qn then
         (match inspect g with
          | Tv_App eq_type_x (y, _) ->
            (match inspect eq_type_x with
             | Tv_App eq_type (x, _) ->
               (match inspect eq_type with
                | Tv_App eq (typ, _) ->
                  (match inspect eq with
                   | Tv_UInst eq _
                   | Tv_FVar eq ->
                     if fv_to_string eq = flatten_name eq2_qn then
                       (x, y)
                     else fail "not an equality"
                   | _ -> fail "not an app2 of fvar: ")
                | _ -> fail "not an app3")
             | _ -> fail "not an app2")
          | _ -> fail "not an app under squash")
       else fail "not a squash"
     | _ -> fail "not an app of fvar at top level")
  | _ -> fail "not an app at top level"

/// …and here's how you could use it:

(* let _ = *)
(*   assert_by_tactic (1 + 1 == 2) *)
(*     (fun () -> let l, r = fetch_eq_side () in *)
(*                print (term_to_string l ^ " / " ^ term_to_string r)) *)

/// This file defines pattern-matching primitives that let you write the same
/// thing like this…
///
/// .. code:: fstar
///
///    let fetch_eq_side' #a () : Tac (term * term) =
///      gpm (fun (left right: a) (g: pm_goal (squash (left == right))) ->
///             (quote left, quote right) <: Tac (term * term))
///
///    let _ =
///      assert_by_tactic (1 + 1 == 2)
///        (fun () -> let l, r = fetch_eq_side' #int () in
///                   print (term_to_string l ^ " / " ^ term_to_string r))
///
/// …or, more succinctly, like this:
///
/// .. code:: fstar
///
///    let _ =
///      assert_by_tactic (1 + 1 == 2)
///        (gpm (fun (left right: int) (g: pm_goal (squash (left == right))) ->
///                let l, r = quote left, quote right in
///                print (term_to_string l ^ " / " ^ term_to_string r) <: Tac unit))


/// Some utility functions
/// ======================
///
/// (Skip over this part on a quick read — these are just convenience functions)


(** Ensure that tactic `t` fails. **)
let mustfail #a (t: unit -> Tac a) (message: string) : Tac unit =
    match trytac t with
    | Some _ -> fail message
    | None -> ()

/// The following two tactics are needed because of issues with the ``Tac``
/// effect.

let implies_intro' () : Tac unit =
  let _ = implies_intro () in ()

let repeat' #a (f: unit -> Tac a) : Tac unit =
  let _ = repeat f in ()

let and_elim' (h: binding) : Tac unit =
  and_elim (pack (Tv_Var h));
  clear h

(** Use a hypothesis at type a to satisfy a goal at type squash a *)
let exact_hyp (a: Type0) (h: namedv) : Tac unit =
  let hd = quote (FStar.Squash.return_squash #a) in
  exact (mk_app hd [((pack (Tv_Var h)), Q_Explicit)])

(** Use a hypothesis h (of type a) to satisfy a goal at type a *)
let exact_hyp' (h: namedv): Tac unit =
  exact (pack (Tv_Var h))

/// Pattern types
/// =============
///
/// Patterns are defined using a simple inductive type, mirroring the structure
/// of ``term_view``.

type varname = string

type qn = string

type pattern =
| PVar: name: varname -> pattern
| PQn: qn: qn -> pattern
| PType: pattern
| PApp: hd: pattern -> arg: pattern -> pattern

let desc_of_pattern = function
| PVar _ -> "a variable"
| PQn qn -> "a constant (" ^ qn ^ ")"
| PType -> "Type"
| PApp _ _ -> "a function application"

let rec string_of_pattern = function
| PVar x -> "?" ^ x
| PQn qn -> qn
| PType -> "Type"
| PApp l r -> "(" ^ string_of_pattern l ^ " "
                 ^ string_of_pattern r ^ ")"

/// Pattern matching exceptions
/// ===========================
///
/// Pattern-matching is defined as a pure, monadic function (because of issues
/// with combining DM4F effects, but also because it helps with debugging).
/// This section defines the exception monad.
///
/// Types of exceptions
/// -------------------

noeq type match_exception =
| NameMismatch of qn & qn
| SimpleMismatch of pattern & term
| NonLinearMismatch of varname & term & term
| UnsupportedTermInPattern of term
| IncorrectTypeInAbsPatBinder of typ

let term_head t : Tac string =
  match inspect t with
  | Tv_Var bv -> "Tv_Var"
  | Tv_BVar fv -> "Tv_BVar"
  | Tv_FVar fv -> "Tv_FVar"
  | Tv_UInst _ _ -> "Tv_UInst"
  | Tv_App f x -> "Tv_App"
  | Tv_Abs x t -> "Tv_Abs"
  | Tv_Arrow x t -> "Tv_Arrow"
  | Tv_Type _ -> "Tv_Type"
  | Tv_Refine x t -> "Tv_Refine"
  | Tv_Const cst -> "Tv_Const"
  | Tv_Uvar i t -> "Tv_Uvar"
  | Tv_Let r attrs b t1 t2 -> "Tv_Let"
  | Tv_Match t _ branches -> "Tv_Match"
  | Tv_AscribedT _ _ _ _ -> "Tv_AscribedT"
  | Tv_AscribedC _ _ _ _ -> "Tv_AscribedC"
  | Tv_Unknown -> "Tv_Unknown"
  | Tv_Unsupp -> "Tv_Unsupp"

let string_of_match_exception = function
  | NameMismatch (qn1, qn2) ->
    "Match failure (name mismatch): expecting " ^
    qn1 ^ ", found " ^ qn2
  | SimpleMismatch (pat, tm) ->
    "Match failure (sort mismatch): expecting " ^
    desc_of_pattern pat ^ ", got " ^ term_to_string tm
  | NonLinearMismatch (nm, t1, t2) ->
    "Match failure (nonlinear mismatch): variable " ^ nm ^
    " needs to match both " ^ (term_to_string t1) ^
    " and " ^ (term_to_string t2)
  | UnsupportedTermInPattern tm ->
    "Match failure (unsupported term in pattern): " ^
    term_to_string tm ^ " (" ^ term_head tm ^ ")"
  | IncorrectTypeInAbsPatBinder typ ->
    "Incorrect type in pattern-matching binder: " ^
    term_to_string typ ^ " (use one of ``var``, ``hyp …``, or ``goal …``)"

/// The exception monad
/// -------------------

noeq type match_res a =
| Success of a
| Failure of match_exception

let return #a (x: a) : match_res a =
  Success x

let (let?) (#a #b: Type)
         (f: match_res a)
         (g: a -> Tac (match_res b))
    : Tac (match_res b) =
  match f with
  | Success aa -> g aa
  | Failure ex -> Failure ex

let raise #a (ex: match_exception) : match_res a =
  Failure ex

/// Liftings
/// --------
///
/// There's a natural lifting from the exception monad into the tactic effect:

let lift_exn_tac #a #b (f: a -> match_res b) (aa: a) : Tac b =
  match f aa with
  | Success bb -> bb
  | Failure ex -> Tactics.fail (string_of_match_exception ex)

let lift_exn_tactic #a #b (f: a -> match_res b) (aa: a) : Tac b =
  match f aa with
  | Success bb -> bb
  | Failure ex -> Tactics.fail (string_of_match_exception ex)

/// Pattern interpretation
/// ======================
///
/// This section implement pattern-matching.  This is strictly a one term, one
/// pattern implementation — handling cases in which mutliple hypotheses match
/// the same pattern is done later.

type bindings = list (varname & term)
let string_of_bindings (bindings: bindings) =
  String.concat "\n"
    (map (fun (nm, tm) -> (">> " ^ nm ^ ": " ^ term_to_string tm))
                  bindings)

(** Match a pattern against a term.
`cur_bindings` is a list of bindings collected while matching previous parts of
the pattern.  Returns a result in the exception monad. **)
let rec interp_pattern_aux (pat: pattern) (cur_bindings: bindings) (tm:term)
    : Tac (match_res bindings) =
  let interp_var (v: varname) cur_bindings tm =
    match List.Tot.Base.assoc v cur_bindings with
    | Some tm' -> if term_eq tm tm' then return cur_bindings
                 else raise (NonLinearMismatch (v, tm, tm'))
    | None -> return ((v, tm) :: cur_bindings) in
  let interp_qn (qn: qn) cur_bindings tm =
    match inspect tm with
    | Tv_UInst fv _
    | Tv_FVar fv ->
      if fv_to_string fv = qn then return cur_bindings
      else raise (NameMismatch (qn, (fv_to_string fv)))
    | _ -> raise (SimpleMismatch (pat, tm)) in
  let interp_type cur_bindings tm =
    match inspect tm with
    | Tv_Type _ -> return cur_bindings
    | _ -> raise (SimpleMismatch (pat, tm)) in
  let interp_app (p_hd p_arg: (p:pattern{p << pat})) cur_bindings tm =
    match inspect tm with
    | Tv_App hd (arg, _) ->
      let? with_hd = interp_pattern_aux p_hd cur_bindings hd in
      let? with_arg = interp_pattern_aux p_arg with_hd arg in
      return with_arg
    | _ -> raise (SimpleMismatch (pat, tm)) in
    match pat with
    | PVar var -> interp_var var cur_bindings tm
    | PQn qn -> interp_qn qn cur_bindings tm
    | PType -> interp_type cur_bindings tm
    | PApp p_hd p_arg -> interp_app p_hd p_arg cur_bindings tm

(** Match a pattern `pat` against a term.
Returns a result in the exception monad. **)
let interp_pattern (pat: pattern) : term -> Tac (match_res bindings) =
  fun (tm: term) ->
    let? rev_bindings = interp_pattern_aux pat [] tm in
    return (List.Tot.Base.rev rev_bindings)

(** Match a term `tm` against a pattern `pat`.
Raises an exception if the match fails.  This is mostly useful for debugging:
use ``mgw`` to capture matches. **)
let match_term pat (tm : term) : Tac bindings =
    match interp_pattern pat (norm_term [] tm) with
    | Success bb -> bb
    | Failure ex -> Tactics.fail (string_of_match_exception ex)

/// Pattern-matching problems
/// =========================
///
/// Generalizing past single-term single-pattern problems, we obtain the
/// following notions of pattern-matching problems and solutions:

let debug msg : Tac unit = () // print msg

/// Definitions
/// -----------

let absvar = binding
type hypothesis = binding

/// A matching problem is composed of holes (``mp_vars``), hypothesis patterns
/// (``mp_hyps``), and a goal pattern (``mp_goal``).

noeq type matching_problem =
  { mp_vars: list varname;
    mp_hyps: list (varname & pattern);
    mp_goal: option pattern }

let string_of_matching_problem mp =
  let vars =
    String.concat ", " mp.mp_vars in
  let hyps =
    String.concat "\n        "
      (List.Tot.Base.map (fun (nm, pat) ->
        nm ^ ": " ^ (string_of_pattern pat)) mp.mp_hyps) in
  let goal = match mp.mp_goal with
             | None -> "_"
             | Some pat -> string_of_pattern pat in
  "\n{ vars: " ^ vars ^ "\n" ^
  "  hyps: " ^ hyps ^ "\n" ^
  "  goal: " ^ goal ^ " }"

/// A solution is composed of terms captured to mach the holes, and binders
/// captured to match hypothesis patterns.

noeq type matching_solution =
  { ms_vars: list (varname & term);
    ms_hyps: list (varname & hypothesis) }

let string_of_matching_solution ms =
  let vars =
    String.concat "\n            "
      (map (fun (varname, tm) ->
        varname ^ ": " ^ (term_to_string tm)) ms.ms_vars) in
  let hyps =
    String.concat "\n        "
      (map (fun (nm, binding) ->
        nm ^ ": " ^ (binding_to_string binding)) ms.ms_hyps) in
  "\n{ vars: " ^ vars ^ "\n" ^
  "  hyps: " ^ hyps ^ " }"

(** Find a varname in an association list; fail if it can't be found. **)
let assoc_varname_fail (#b: Type) (key: varname) (ls: list (varname & b))
    : Tac b =
  match List.Tot.Base.assoc key ls with
  | None -> fail ("Not found: " ^ key)
  | Some x -> x

let ms_locate_hyp (a: Type) (solution: matching_solution)
                  (name: varname) : Tac hypothesis =
  assoc_varname_fail name solution.ms_hyps

let ms_locate_var (a: Type) (solution: matching_solution)
                  (name: varname) : Tac a =
  unquote #a (assoc_varname_fail name solution.ms_vars)

let ms_locate_unit (a: Type) _solution _binder_name : Tac unit =
  ()

/// Resolution
/// ----------
///
/// Solving a matching problem is a two-steps process: find an initial
/// assignment for holes based on the goal pattern, then find a set of
/// hypotheses matching hypothesis patterns.
///
/// Note that the implementation takes a continuation of type
/// ``matching_solution -> Tac a``.  This continuation is needed because we want
/// users to be able to provide extra criteria on matching solutions (most
/// commonly, this criterion is that a particular tactic should run
/// successfuly).
///
/// This makes it easy to implement a simple for of search through the context,
/// where one can find a hypothesis matching a particular predicate by
/// constructing a trivial matching problem and passing the predicate as the
/// continuation.

(** Scan ``hypotheses`` for a match for ``pat`` that lets ``body`` succeed.

``name`` is used to refer to the hypothesis matched in the final solution.
``part_sol`` includes bindings gathered while matching previous solutions. **)
let rec solve_mp_for_single_hyp #a
                                (name: varname)
                                (pat: pattern)
                                (hypotheses: list hypothesis)
                                (body: matching_solution -> Tac a)
                                (part_sol: matching_solution)
    : Tac a =
  match hypotheses with
  | [] ->
    fail #a "No matching hypothesis"
  | h :: hs ->
    or_else // Must be in ``Tac`` here to run `body`
      (fun () ->
         match interp_pattern_aux pat part_sol.ms_vars (type_of_binding h) with
         | Failure ex ->
           fail ("Failed to match hyp: " ^ (string_of_match_exception ex))
         | Success bindings ->
           let ms_hyps = (name, h) :: part_sol.ms_hyps in
           body ({ part_sol with ms_vars = bindings; ms_hyps = ms_hyps }))
      (fun () ->
         solve_mp_for_single_hyp name pat hs body part_sol)

(** Scan ``hypotheses`` for matches for ``mp_hyps`` that lets ``body``
succeed. **)
let rec solve_mp_for_hyps #a
                          (mp_hyps: list (varname & pattern))
                          (hypotheses: list hypothesis)
                          (body: matching_solution -> Tac a)
                          (partial_solution: matching_solution)
    : Tac a =
  match mp_hyps with
  | [] -> body partial_solution
  | (name, pat) :: pats ->
    solve_mp_for_single_hyp name pat hypotheses
      (solve_mp_for_hyps pats hypotheses body)
      partial_solution

(** Solve a matching problem.

The solution returned is constructed to ensure that the continuation ``body``
succeeds: this implements the usual backtracking-match semantics. **)
let solve_mp #a (problem: matching_problem)
                (hypotheses: list hypothesis) (goal: term)
                (body: matching_solution -> Tac a)
    : Tac a =
  let goal_ps =
    match problem.mp_goal with
    | None -> { ms_vars = []; ms_hyps = [] }
    | Some pat ->
      match interp_pattern pat goal with
      | Failure ex -> fail ("Failed to match goal: " ^ (string_of_match_exception ex))
      | Success bindings -> { ms_vars = bindings; ms_hyps = [] } in
  solve_mp_for_hyps #a problem.mp_hyps hypotheses body goal_ps

/// A DSL for pattern-matching
/// ==========================
///
/// Using pattern-matching problems as defined above is relatively cumbersome,
/// so we now introduce a lightweight notation, in two steps: pattern notations,
/// and matching-problem notations.
///
/// Pattern notations
/// -----------------
///
/// The first part of our pattern-matching syntax is pattern notations: we
/// provide a reflective function which constructs a pattern from a term:
/// variables are holes, free variables are constants, and applications are
/// application patterns.

(* FIXME: MOVE *)
let name_of_namedv (x:namedv) : Tac string =
  unseal (inspect_namedv x).ppname

(** Compile a term `tm` into a pattern. **)
let rec pattern_of_term_ex tm : Tac (match_res pattern) =
  match inspect tm with
  | Tv_Var bv ->
    return (PVar (name_of_namedv bv))
  | Tv_FVar fv
  | Tv_UInst fv _ ->
    let qn = fv_to_string fv in
    return (PQn qn)
  | Tv_Type _ ->
    return PType
  | Tv_App f (x, _) ->
     let? fpat = pattern_of_term_ex f in
     let? xpat = pattern_of_term_ex x in
     return (PApp fpat xpat)
  | _ -> raise (UnsupportedTermInPattern tm)

(** β-reduce a term `tm`.
This is useful to remove needles function applications introduced by F*, like
``(fun a b c -> a) 1 2 3``. **)
let beta_reduce (tm: term) : Tac term =
  norm_term [] tm

(** Compile a term `tm` into a pattern. **)
let pattern_of_term tm : Tac pattern =
    match pattern_of_term_ex tm with
    | Success bb -> bb
    | Failure ex -> Tactics.fail (string_of_match_exception ex)

/// Problem notations
/// -----------------
///
/// We then introduce a DSL for matching problems, best explained on the
/// following example::
///
/// (fun (a b c: ①) (h1 h2 h3: hyp ②) (g: pm_goal ③) → ④)
///
/// This notation is intended to express a pattern-matching problems with three
/// holes ``a``, ``b``, and ``c`` of type ①, matching hypotheses ``h1``, ``h2``,
/// and ``h3`` against pattern ② and the goal against the pattern ③.  The body
/// of the notation (④) is then run with appropriate terms bound to ``a``,
/// ``b``, and ``c``, appropriate binders bound to ``h1``, ``h2``, and ``h3``,
/// and ``()`` bound to ``g``.
///
/// We call these patterns ``abspat``s (abstraction patterns), and we provide
/// facilities to parse them into matching problems, and to run their bodies
/// against a particular matching solution.

// We used to annotate variables with an explicit 'var' marker, but then that
// var annotation leaked into the types of other hypotheses due to type
// inference, requiring non-trivial normalization.

// let var (a: Type) = a
let hyp (a: Type) = binding
let pm_goal (a: Type) = unit

let hyp_qn  = `%hyp
let goal_qn = `%pm_goal

noeq type abspat_binder_kind =
| ABKVar of typ
| ABKHyp
| ABKGoal

let string_of_abspat_binder_kind = function
  | ABKVar _ -> "varname"
  | ABKHyp -> "hyp"
  | ABKGoal -> "goal"

noeq type abspat_argspec =
  { asa_name: absvar;
    asa_kind: abspat_binder_kind }

// We must store this continuation, because recomputing it yields different
// names when the binders are re-opened.
type abspat_continuation =
  list abspat_argspec & term

let type_of_named_binder (nb : binder) : term =
 nb.sort

let classify_abspat_binder (b : binder): Tac (abspat_binder_kind & term) =
  let varname = "v" in
  let hyp_pat = PApp (PQn hyp_qn) (PVar varname) in
  let goal_pat = PApp (PQn goal_qn) (PVar varname) in

  let typ = type_of_named_binder b in
  match interp_pattern hyp_pat typ with
  | Success [(_, hyp_typ)] -> ABKHyp, hyp_typ
  | Success _ -> fail "classifiy_abspat_binder: impossible (1)"
  | Failure _ ->
    match interp_pattern goal_pat typ with
    | Success [(_, goal_typ)] -> ABKGoal, goal_typ
    | Success _ -> fail "classifiy_abspat_binder: impossible (2)"
    | Failure _ -> ABKVar typ, typ

(** Split an abstraction `tm` into a list of binders and a body. **)
let rec binders_and_body_of_abs tm : Tac (list binder & term) =
  match inspect tm with
  | Tv_Abs binder tm ->
    let binders, body = binders_and_body_of_abs tm in
    binder :: binders, body
  | _ -> [], tm

let cleanup_abspat (t: term) : Tac term =
  norm_term [] t


let name_of_named_binder (nb : binder) : Tac string =
 unseal nb.ppname

(** Parse a notation into a matching problem and a continuation.

Pattern-matching notations are of the form ``(fun binders… -> continuation)``,
where ``binders`` are of one of the forms ``var …``, ``hyp …``, or ``goal …``.
``var`` binders are typed holes to be used in other binders; ``hyp`` binders
indicate a pattern to be matched against hypotheses; and ``goal`` binders match
the goal.


A reduction phase is run to ensure that the pattern looks reasonable; it is
needed because F* tends to infer arguments in β-expanded form.

The continuation returned can't directly be applied to a pattern-matching
solution; see ``interp_abspat_continuation`` below for that. **)
let matching_problem_of_abs (tm: term)
    : Tac (matching_problem & abspat_continuation) =

  let binders, body = binders_and_body_of_abs (cleanup_abspat tm) in
  debug ("Got binders: " ^ (String.concat ", "
         (map (fun b -> name_of_named_binder b <: Tac string) binders)));

  let classified_binders : list (binder & string & abspat_binder_kind & typ) =
    map (fun binder ->
        let bv_name = name_of_named_binder binder in
        debug ("Got binder: " ^ bv_name ^ "; type is " ^
               term_to_string (type_of_named_binder binder));
        let binder_kind, typ = classify_abspat_binder binder in
        (binder, bv_name, binder_kind, typ))
      binders in

  let problem =
    fold_left
      (fun problem (binder, bv_name, binder_kind, typ) ->
         debug ("Compiling binder " ^ name_of_named_binder binder ^
                ", classified as " ^ string_of_abspat_binder_kind binder_kind ^
                ", with type " ^ term_to_string typ);
         match binder_kind with
         | ABKVar _ -> { problem with mp_vars = bv_name :: problem.mp_vars }
         | ABKHyp -> { problem with mp_hyps = (bv_name, (pattern_of_term typ))
                                             :: problem.mp_hyps }
         | ABKGoal -> { problem with mp_goal = Some (pattern_of_term typ) })
      ({ mp_vars = []; mp_hyps = []; mp_goal = None })
      classified_binders in

  let continuation =
    let abspat_argspec_of_binder xx : Tac abspat_argspec =
    match xx with | (binder, xx, binder_kind, yy)  ->
      { asa_name = binder_to_binding binder; asa_kind = binder_kind } in
    (map abspat_argspec_of_binder classified_binders, tm) in

  let mp =
    { mp_vars = List.Tot.Base.rev #varname problem.mp_vars;
      mp_hyps = List.Tot.Base.rev #(varname & pattern) problem.mp_hyps;
      mp_goal = problem.mp_goal } in

  debug ("Got matching problem: " ^ (string_of_matching_problem mp));
  mp, continuation

/// Continuations
/// -------------
///
/// Parsing an abspat yields a matching problem and a continuation of type
/// ``abspat_continuation``, which is essentially just a list of binders and a
/// term (the body of the abstraction pattern).

(** Get the (quoted) type expected by a specific kind of abspat binder. **)
let arg_type_of_binder_kind binder_kind : Tac term =
  match binder_kind with
  | ABKVar typ -> typ
  | ABKHyp -> `binder
  | ABKGoal -> `unit

(** Retrieve the function used to locate a value for a given abspat binder. **)
let locate_fn_of_binder_kind binder_kind =
  match binder_kind with
  | ABKVar _ -> `ms_locate_var
  | ABKHyp   -> `ms_locate_hyp
  | ABKGoal  -> `ms_locate_unit

(** Construct a term fetching the value of an abspat argument from a quoted
matching solution ``solution_term``. **)
let abspat_arg_of_abspat_argspec solution_term (argspec: abspat_argspec)
    : Tac term =
  let loc_fn = locate_fn_of_binder_kind argspec.asa_kind in
  let name_tm = pack (Tv_Const (C_String (unseal argspec.asa_name.ppname))) in
  let locate_args = [(arg_type_of_binder_kind argspec.asa_kind, Q_Explicit);
                     (solution_term, Q_Explicit); (name_tm, Q_Explicit)] in
  mk_app loc_fn locate_args

(** Specialize a continuation of type ``abspat_continuation``.
This constructs a fully applied version of `continuation`, but it requires a
quoted solution to be passed in. **)

let rec hoist_and_apply (head:term) (arg_terms:list term) (hoisted_args:list argv)
  : Tac term =
  match arg_terms with
  | [] -> mk_app head (List.rev hoisted_args)
  | arg_term::rest ->
    let n = List.Tot.length hoisted_args in
    //let bv = fresh_bv_named ("x" ^ (string_of_int n)) in
    let nb : binder = {
      ppname = seal ("x" ^ string_of_int n);
      sort = pack Tv_Unknown;
      uniq = fresh ();
      qual = Q_Explicit;
      attrs = [] ;
    }
    in
    pack (Tv_Let false [] nb arg_term (hoist_and_apply head rest ((pack (Tv_Var (binder_to_namedv nb)), Q_Explicit)::hoisted_args)))
  
let specialize_abspat_continuation' (continuation: abspat_continuation)
                                    (solution_term:term)
    : Tac term =
  let mk_arg_term argspec =
    abspat_arg_of_abspat_argspec solution_term argspec in
  let argspecs, body = continuation in
  hoist_and_apply body (map mk_arg_term argspecs) []

(** Specialize a continuation of type ``abspat_continuation``.  This yields a
quoted function taking a matching solution and running its body with appropriate
bindings. **)
let specialize_abspat_continuation (continuation: abspat_continuation)
    : Tac term =
  let solution_binder = fresh_binder (`matching_solution) in
  let solution_term = pack (Tv_Var (binder_to_namedv solution_binder)) in
  let applied = specialize_abspat_continuation' continuation solution_term in
  let thunked = pack (Tv_Abs solution_binder applied) in
  debug ("Specialized into " ^ (term_to_string thunked));
  let normalized = beta_reduce thunked in
  debug ("… which reduces to " ^ (term_to_string normalized));
  thunked

(** Interpret a continuation of type ``abspat_continuation``.
This yields a function taking a matching solution and running the body of the
continuation with appropriate bindings. **)
let interp_abspat_continuation (a:Type0) (continuation: abspat_continuation)
    : Tac (matching_solution -> Tac a) =
  let applied = specialize_abspat_continuation continuation in
  unquote #(matching_solution -> Tac a) applied

/// Putting it all together
/// =======================
///
/// We now have all we need to use pattern-matching, short of a few convenience functions:

(** Construct a matching problem from an abspat. **)
let interp_abspat #a (abspat: a)
    : Tac (matching_problem & abspat_continuation) =
  matching_problem_of_abs (quote abspat)

(** Construct an solve a matching problem.
This higher-order function isn't very usable on its own — it's mostly a
convenience function to avoid duplicating the problem-parsing code. **)
let match_abspat #b #a (abspat: a)
                 (k: abspat_continuation -> Tac (matching_solution -> Tac b))
    : Tac b =
  let goal = cur_goal () in
  let hypotheses = vars_of_env (cur_env ()) in
  let problem, continuation = interp_abspat abspat in
  solve_mp problem hypotheses goal (k continuation)

(** Inspect the matching problem produced by parsing an abspat. **)
let inspect_abspat_problem #a (abspat: a) : Tac matching_problem =
  fst (interp_abspat #a abspat)

(** Inspect the matching solution produced by parsing and solving an abspat. **)
let inspect_abspat_solution #a (abspat: a) : Tac matching_solution =
  match_abspat abspat (fun _ -> (fun solution -> solution <: Tac _) <: Tac _)

let tpair #a #b (x : a) : Tac (b -> Tac (a & b)) =
  fun (y: b) -> (x, y)

/// Our first convenient entry point!
///
/// This takes an abspat, parses it, computes a solution, and runs the body of
/// the abspat with appropriate bindings.  It implements what others call ‘lazy’
/// pattern-matching, so called because the success of the body of the pattern
/// isn't taken into account when deciding whether a particular set of matched
/// hypothesis should be retained.  In other words, it picks the first matching
/// set of hypotheses, and commits to it.
///
/// If you think that sounds like a greedy algorithm, it does.  That's why it's
/// called ‘gpm’ below: greedy pattern-matching.

(** Solve a greedy pattern-matching problem and run its continuation.
This if for pattern-matching problems in the ``Tac`` effect. **)
let gpm #b #a (abspat: a) () : Tac b =
  let continuation, solution = match_abspat abspat tpair in
  interp_abspat_continuation b continuation solution

/// And here's the non-greedy version of the same.  It's informative to compare
/// the implementations!  This one will only find assignments that let the body
/// run successfuly.

(** Solve a greedy pattern-matching problem and run its continuation.
This if for pattern-matching problems in the ``Tac`` effect. **)
let pm #b #a (abspat: a) : Tac b =
  match_abspat abspat (interp_abspat_continuation b)

/// Examples
/// ========
///
/// We conclude with a small set of examples.

/// Simple examples
/// ---------------
///
/// Here's the example from the intro, which we can now run!

let fetch_eq_side' #a : Tac (term & term) =
  gpm (fun (left right: a) (g: pm_goal (squash (left == right))) ->
         (quote left, quote right)) ()

(* let _ = *)
(*   assert_by_tactic (1 + 1 == 2) *)
(*     (fun () -> let l, r = fetch_eq_side' #int in *)
(*                print (term_to_string l ^ " / " ^ term_to_string r)) *)

(* let _ = *)
(*   assert_by_tactic (1 + 1 == 2) *)
(*     (gpm (fun (left right: int) (g: pm_goal (squash (left == right))) -> *)
(*             let l, r = quote left, quote right in *)
(*             print (term_to_string l ^ " / " ^ term_to_string r) <: Tac unit)) *)

/// Commenting out the following example and comparing ``pm`` and ``gpm`` can be
/// instructive:

// let test_bt (a: Type0) (b: Type0) (c: Type0) (d: Type0) =
//   assert_by_tactic ((a ==> d) ==> (b ==> d) ==> (c ==> d) ==> a ==> d)
//     (fun () -> repeat' implies_intro';
//                gpm (fun (a b: Type0) (h: hyp (a ==> b)) ->
//                            print (binder_to_string h);
//                            fail "fail here" <: Tac unit);
//                qed ())

/// A real-life example
/// -------------------
///
/// The following tactics combines mutliple simple building blocks to solve a
/// goal.  Each use of ``lpm`` recognizes a specific pattern; and each tactic is
/// tried in succession, until one succeeds.  The whole process is repeated as
/// long as at least one tactic succeeds.

(* let example (#a:Type0) (#b:Type0) (#c:Type0) :unit = *)
(*   assert_by_tactic (a /\ b ==> c == b ==> c) *)
(*     (fun () -> repeat' (fun () -> *)
(*                  gpm #unit (fun (a: Type) (h: hyp (squash a)) -> *)
(*                               clear h <: Tac unit) `or_else` *)
(*                  (fun () -> gpm #unit (fun (a b: Type0) (g: pm_goal (squash (a ==> b))) -> *)
(*                               implies_intro' () <: Tac unit) `or_else` *)
(*                  (fun () -> gpm #unit (fun (a b: Type0) (h: hyp (a /\ b)) -> *)
(*                               and_elim' h <: Tac unit) `or_else` *)
(*                  (fun () -> gpm #unit (fun (a b: Type0) (h: hyp (a == b)) (g: pm_goal (squash a)) -> *)
(*                               rewrite h <: Tac unit) `or_else` *)
(*                  (fun () -> gpm #unit (fun (a: Type0) (h: hyp a) (g: pm_goal (squash a)) -> *)
(*                               exact_hyp a h <: Tac unit) ()))))); *)
(*                qed ()) *)

/// Possible extensions
/// ===================
///
/// The following tasks would make for interesting extensions of this
/// experiment:
///
/// - Handling multiple goal patterns (easy)
/// - Extending the matching language (match under binders?)
/// - Introducing specialized syntax
/// - Thinking about a sound way of supporting ‘match-anything’ patterns in
///   abspat notations
/// - Using the normalizer to partially-evaluated pattern-matching tactics
/// - Migrating to a compile-time version of ``quote``

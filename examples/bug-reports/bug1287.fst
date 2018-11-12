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

/// GM: Minimized it somewhat. Original file is in examples/pattern-matching

// NOTE: The name of this module is mentioned down below
// If you change it, make sure to do it everywhere.
module Bug1287

open FStar.Tactics

#set-options "--admit_smt_queries true"

(** Like ``List.Tot.map``, for tactics. **)
let rec tacmap (f: 'a -> Tac 'b) (ls: list 'a) : Tac (list 'b) =
  match ls with
  | [] -> []
  | hd :: tl -> f hd :: tacmap f tl

(** Like ``List.Tot.fold_left``, for tactics. **)
let rec tacfold_left (f: 'a -> 'b -> Tac 'a) (x: 'a) (l:list 'b)
        : Tac 'a (decreases l) =
  match l with
  | [] -> x
  | hd :: tl -> tacfold_left f (f x hd) tl

let implies_intro' () : Tac unit =
  let _ = implies_intro () in ()

let repeat' #a (f: unit -> Tac a) : Tac unit =
  let _ = repeat f in ()

let and_elim' (h: binder) : Tac unit =
  and_elim (pack (Tv_Var h));
  clear h

let exact_hyp (a: Type0) (h: binder) : Tac unit =
  let hd = quote (FStar.Squash.return_squash #a) in
  exact (mk_app hd [((pack (Tv_Var h)), Q_Explicit)])

type varname = string

type qn = list string
let string_of_qn qn = String.concat "." qn

type pattern =
| PAny: pattern
| PVar: name: varname -> pattern
| PQn: qn: qn -> pattern
| PType: pattern
| PApp: hd: pattern -> arg: pattern -> pattern

let desc_of_pattern = function
| PAny -> "anything"
| PVar _ -> "a variable"
| PQn qn -> "a constant (" ^ string_of_qn qn ^ ")"
| PType -> "Type"
| PApp _ _ -> "a function application"

let rec string_of_pattern = function
| PAny -> "__"
| PVar x -> "?" ^ x
| PQn qn -> string_of_qn qn
| PType -> "Type"
| PApp l r -> "(" ^ string_of_pattern l ^ " "
                 ^ string_of_pattern r ^ ")"

noeq type match_exception =
| NameMismatch of qn * qn
| SimpleMismatch of pattern * term
| NonLinearMismatch of varname * term * term
| UnsupportedTermInPattern of term
| IncorrectTypeInAbsPatBinder of typ

let term_head t : string =
  match inspect t with
  | Tv_Var bv -> "Tv_Var"
  | Tv_FVar fv -> "Tv_FVar"
  | Tv_App f x -> "Tv_App"
  | Tv_Abs x t -> "Tv_Abs"
  | Tv_Arrow x t -> "Tv_Arrow"
  | Tv_Type () -> "Tv_Type"
  | Tv_Refine x t -> "Tv_Refine"
  | Tv_Const cst -> "Tv_Const"
  | Tv_Uvar i t -> "Tv_Uvar"
  | Tv_Let r b t1 t2 -> "Tv_Let"
  | Tv_Match t branches -> "Tv_Match"
  | Tv_Unknown -> "Tv_Unknown"

let string_of_match_exception = function
  | NameMismatch (qn1, qn2) ->
    "Match failure (name mismatch): expecting " ^
    (string_of_qn qn1) ^ ", found " ^ (string_of_qn qn2)
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

let lift_exn_tac #a #b (f: a -> match_res b) (aa: a) : Tac b =
  match f aa with
  | Success bb -> bb
  | Failure ex -> Tactics.fail (string_of_match_exception ex)

type bindings = list (varname * term)

(** Match a pattern against a term.
`cur_bindings` is a list of bindings collected while matching previous parts of
the pattern.  Returns a result in the exception monad. **)
let rec interp_pattern_aux (pat: pattern) (cur_bindings: bindings) (tm:term)
    : match_res bindings =
  let interp_any () cur_bindings tm =
    return [] in
  let interp_var (v: varname) cur_bindings tm =
    match List.Tot.assoc v cur_bindings with
    | Some tm' -> if term_eq tm tm' then return cur_bindings
                 else raise (NonLinearMismatch (v, tm, tm'))
    | None -> return ((v, tm) :: cur_bindings) in
  let interp_qn (qn: qn) cur_bindings tm =
    match inspect tm with
    | Tv_FVar fv ->
      if inspect_fv fv = qn then return cur_bindings
      else raise (NameMismatch (qn, (inspect_fv fv)))
    | _ -> raise (SimpleMismatch (pat, tm)) in
  let interp_type cur_bindings tm =
    match inspect tm with
    | Tv_Type () -> return cur_bindings
    | _ -> raise (SimpleMismatch (pat, tm)) in
  let interp_app (p_hd p_arg: (p:pattern{p << pat})) cur_bindings tm =
    match inspect tm with
    | Tv_App hd (arg, _) ->
      with_hd <-- interp_pattern_aux p_hd cur_bindings hd;
      with_arg <-- interp_pattern_aux p_arg with_hd arg;
      return with_arg
    | _ -> raise (SimpleMismatch (pat, tm)) in
    match pat with
    | PAny -> interp_any () cur_bindings tm
    | PVar var -> interp_var var cur_bindings tm
    | PQn qn -> interp_qn qn cur_bindings tm
    | PType -> interp_type cur_bindings tm
    | PApp p_hd p_arg -> interp_app p_hd p_arg cur_bindings tm

(** Match a pattern `pat` against a term.
Returns a result in the exception monad. **)
let interp_pattern (pat: pattern) : term -> match_res bindings =
  fun (tm: term) ->
    rev_bindings <-- interp_pattern_aux pat [] tm;
    return (List.Tot.rev rev_bindings)

(** Match a term `tm` against a pattern `pat`.
Raises an exception if the match fails.  This is mostly useful for debugging:
use ``mgw`` to capture matches. **)
let match_term pat : term -> Tac bindings =
  fun tm ->
    lift_exn_tac (interp_pattern pat) (norm_term [] tm)

let debug msg : Tac unit = () 

let absvar : eqtype = binder
type hypothesis = binder

noeq type matching_problem =
  { mp_vars: list varname;
    mp_hyps: list (varname * pattern);
    mp_goal: option pattern }

let string_of_matching_problem mp =
  let vars =
    String.concat ", " mp.mp_vars in
  let hyps =
    String.concat "\n        "
      (List.Tot.map (fun (nm, pat) ->
        nm ^ ": " ^ (string_of_pattern pat)) mp.mp_hyps) in
  let goal = match mp.mp_goal with
             | None -> "_"
             | Some pat -> string_of_pattern pat in
  "\n{ vars: " ^ vars ^ "\n" ^
  "  hyps: " ^ hyps ^ "\n" ^
  "  goal: " ^ goal ^ " }"

noeq type matching_solution =
  { ms_vars: list (varname * term);
    ms_hyps: list (varname * hypothesis) }

let string_of_matching_solution ms =
  let vars =
    String.concat "\n            "
      (List.Tot.map (fun (varname, tm) ->
        varname ^ ": " ^ (term_to_string tm)) ms.ms_vars) in
  let hyps =
    String.concat "\n        "
      (List.Tot.map (fun (nm, binder) ->
        nm ^ ": " ^ (inspect_bv binder)) ms.ms_hyps) in
  "\n{ vars: " ^ vars ^ "\n" ^
  "  hyps: " ^ hyps ^ " }"

(** Find a varname in an association list; fail if it can't be found. **)
let assoc_varname_fail (#b: Type) (key: varname) (ls: list (varname * b))
    : Tac b =
  match List.Tot.assoc key ls with
  | None -> fail ("Not found: " ^ key)
  | Some x -> x

let ms_locate_hyp (a: Type) (solution: matching_solution)
                  (name: varname) : Tac binder =
  assoc_varname_fail name solution.ms_hyps

let ms_locate_var (a: Type) (solution: matching_solution)
                  (name: varname) : Tac a =
  admit ();
  unquote #a (assoc_varname_fail name solution.ms_vars)

let ms_locate_unit (a: Type) _solution _binder_name : Tac unit =
  ()

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
  admit ();
  match hypotheses with
  | [] ->
    fail #a "No matching hypothesis"
  | h :: hs ->
    or_else 
      (fun () ->
         match interp_pattern_aux pat part_sol.ms_vars (type_of_binder h) with
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
                          (mp_hyps: list (varname * pattern))
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
                (hypotheses: binders) (goal: term)
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

assume val __ : #t:Type -> t
let any_qn = ["Bug1287"; "__"]

(** Compile a term `tm` into a pattern. **)
let rec pattern_of_term_ex tm : match_res pattern =
  match inspect tm with
  | Tv_Var bv ->
    return (PVar (inspect_bv bv))
  | Tv_FVar fv ->
    let qn = inspect_fv fv in
    return (if qn = any_qn then PAny else PQn qn)
  | Tv_Type () ->
    return PType
  | Tv_App f (x, _) ->
    let is_any = match inspect f with
                 | Tv_FVar fv -> inspect_fv fv = any_qn
                 | _ -> false in
    if is_any then
      return PAny
    else
      (fpat <-- pattern_of_term_ex f;
       xpat <-- pattern_of_term_ex x;
       return (PApp fpat xpat))
  | _ -> raise (UnsupportedTermInPattern tm)

(** Compile a term `tm` into a pattern. **)
let pattern_of_term tm : Tac pattern =
  admit ();
  lift_exn_tac pattern_of_term_ex tm

let hyp (a: Type) = binder
let goal (a: Type) = unit

let hyp_qn = ["Bug1287"; "hyp"]
let goal_qn = ["Bug1287"; "goal"]

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

type abspat_continuation =
  list abspat_argspec * term

let classify_abspat_binder binder : Tot (abspat_binder_kind * term) =
  admit ();
  let varname = "v" in
  let hyp_pat = PApp (PQn hyp_qn) (PVar varname) in
  let goal_pat = PApp (PQn goal_qn) (PVar varname) in

  let typ = type_of_binder binder in
  match interp_pattern hyp_pat typ with
  | Success [(_, hyp_typ)] -> ABKHyp, hyp_typ
  | Failure _ ->
    match interp_pattern goal_pat typ with
    | Success [(_, goal_typ)] -> ABKGoal, goal_typ
    | Failure _ -> ABKVar typ, typ

(** Split an abstraction `tm` into a list of binders and a body. **)
let rec binders_and_body_of_abs tm : binders * term =
  match inspect tm with
  | Tv_Abs binder tm ->
    let binders, body = binders_and_body_of_abs tm in
    binder :: binders, body
  | _ -> [], tm

let cleanup_abspat (t: term) : Tac term =
  norm_term [] t

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
    : Tac (matching_problem * abspat_continuation) =
  admit ();

  let binders, body = binders_and_body_of_abs (cleanup_abspat tm) in
  debug ("Got binders: " ^ (String.concat ", "
         (List.Tot.map inspect_bv binders)));

  let classified_binders =
    tacmap (fun binder ->
        let bv_name = inspect_bv binder in
        debug ("Got binder: " ^ bv_name ^ "; type is " ^
               term_to_string (type_of_binder binder));
        let binder_kind, typ = classify_abspat_binder binder in
        (binder, bv_name, binder_kind, typ))
      binders in

  let problem =
    tacfold_left
      (fun problem (binder, bv_name, binder_kind, typ) ->
         debug ("Compiling binder " ^ inspect_bv binder ^
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
    let abspat_argspec_of_binder (binder, _, binder_kind, _) : abspat_argspec =
      { asa_name = binder; asa_kind = binder_kind } in
    (List.Tot.map abspat_argspec_of_binder classified_binders, tm) in

  let mp =
    { mp_vars = List.rev #varname problem.mp_vars;
      mp_hyps = List.rev #(varname * pattern) problem.mp_hyps;
      mp_goal = problem.mp_goal } in

  debug ("Got matching problem: " ^ (string_of_matching_problem mp));
  mp, continuation

(** Get the (quoted) type expected by a specific kind of abspat binder. **)
let arg_type_of_binder_kind binder_kind : Tac term =
  match binder_kind with
  | ABKVar typ -> typ
  | ABKHyp -> quote binder
  | ABKGoal -> quote unit

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
  admit ();
  let loc_fn = locate_fn_of_binder_kind argspec.asa_kind in
  let name_tm = pack (Tv_Const (C_String (inspect_bv argspec.asa_name))) in
  let locate_args = [(arg_type_of_binder_kind argspec.asa_kind, Q_Explicit);
                     (solution_term, Q_Explicit); (name_tm, Q_Explicit)] in
  mk_app loc_fn locate_args

(** Specialize a continuation of type ``abspat_continuation``.
This constructs a fully applied version of `continuation`, but it requires a
quoted solution to be passed in. **)
let specialize_abspat_continuation' (continuation: abspat_continuation)
                                    (solution_term:term)
    : Tac term =
  admit ();
  let mk_arg argspec =
    (abspat_arg_of_abspat_argspec solution_term argspec, Q_Explicit) in
  let argspecs, body = continuation in
  mk_app body (tacmap mk_arg argspecs)

(** Specialize a continuation of type ``abspat_continuation``.  This yields a
quoted function taking a matching solution and running its body with appropriate
bindings. **)
let specialize_abspat_continuation (continuation: abspat_continuation)
    : Tac term =
  admit ();
  let solution_binder = fresh_binder (quote matching_solution) in
  let solution_term = pack (Tv_Var solution_binder) in
  let applied = specialize_abspat_continuation' continuation solution_term in
  let thunked = pack (Tv_Abs solution_binder applied) in
  debug ("Specialized into " ^ (term_to_string thunked));
  
  thunked

(** Interpret a continuation of type ``abspat_continuation``.
This yields a function taking a matching solution and running the body of the
continuation with appropriate bindings. **)
let interp_abspat_continuation a (continuation: abspat_continuation)
    : Tac (matching_solution -> Tac a) =
  admit ();
  let applied = specialize_abspat_continuation continuation in
  unquote #(matching_solution -> Tac a) applied

(** Construct a matching problem from an abspat. **)
let interp_abspat #a (abspat: a)
    : Tac (matching_problem * abspat_continuation) =
  admit ();
  let abs = quote abspat in
  matching_problem_of_abs abs

(** Construct an solve a matching problem.
This higher-order function isn't very usable on its own — it's mostly a
convenience function to avoid duplicating the problem-parsing code. **)
let match_abspat #b #a (abspat: a)
                 (k: abspat_continuation -> Tac (matching_solution -> Tac b))
    : Tac b =
  admit ();
  let goal = cur_goal () in
  let hypotheses = binders_of_env (cur_env ()) in
  let problem, continuation = interp_abspat abspat in
  solve_mp #matching_solution problem hypotheses goal (k continuation)

let tpair #a #b : a -> Tac (b -> Tac (a * b)) =
  fun (x: a) -> (fun (y: b) -> (x, y) <: Tac _) <: Tac _

(** Solve a greedy pattern-matching problem and run its continuation.
This if for pattern-matching problems in the ``Tac`` effect. **)
val gpm : #b:Type -> #a:Type -> a -> unit -> Tac b
let gpm #b #a (abspat : a) : unit -> Tac b =
  admit ();
  fun () ->
    let continuation, solution = match_abspat abspat tpair in
    interp_abspat_continuation b continuation solution

open FStar.Tactics // needed again because we overrode return and bind

let example #a #b #c: unit =
  assert_by_tactic (a /\ b ==> c == b ==> c)
    (fun () -> repeat'
       (fun () -> gpm #unit (fun (a: Type) (h: hyp (squash a)) ->
                    clear h <: Tac unit) `or_else`
       (fun () -> gpm #unit (fun (a b: Type0) (g: goal (squash (a ==> b))) ->
                    implies_intro' () <: Tac unit) `or_else`
       (fun () -> gpm #unit (fun (a b: Type0) (h: hyp (a /\ b)) ->
                    and_elim' h <: Tac unit) `or_else`
       (fun () -> gpm #unit (fun (a b: Type0) (h: hyp (a == b)) (g: goal (squash a)) ->
                    rewrite h <: Tac unit) `or_else`
       gpm #unit (fun (a: Type0) (h: hyp a) (g: goal (squash a)) ->
                    exact_hyp a h <: Tac unit)))));
      qed ())

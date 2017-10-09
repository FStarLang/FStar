module PatternMatching

open FStar.Tactics

open PatternMatching.Types
open PatternMatching.Utils
open PatternMatching.Exceptions

type bindings = list (varname * term)

let string_of_bindings (bindings: bindings) =
  String.concat "\n"
    (List.Tot.map (fun (nm, tm) -> (">> " ^ nm ^ ": " ^ term_to_string tm))
                  bindings)

/// Pattern interpretation
/// ======================

(** Match a pattern against a term.
`cur_bindings` is a list of bindings colelcted while matching previous parts of
the pattern.  Returns a result in the exception monad. **)
let rec interp_pattern_aux (pat: pattern) (cur_bindings: bindings)
    : term -> match_res bindings =
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
  let interp_app (p_hd p_arg: p:pattern{p << pat}) cur_bindings tm =
    match inspect tm with
    | Tv_App hd (arg, _) ->
      with_hd <-- interp_pattern_aux p_hd cur_bindings hd;
      with_arg <-- interp_pattern_aux p_arg with_hd arg;
      return with_arg
    | _ -> raise (SimpleMismatch (pat, tm)) in
  fun (tm: term) ->
    match pat with
    | PAny -> interp_any () cur_bindings tm
    | PVar var -> interp_var var cur_bindings tm
    | PQn qn -> interp_qn qn cur_bindings tm
    | PType -> interp_type cur_bindings tm
    | PApp p_hd p_arg -> interp_app p_hd p_arg cur_bindings tm

(** Match it against a term.
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
    lift_exn_tac (interp_pattern pat) (norm_term [] tm ())

/// Pattern notations
/// =================

assume val __ : #t:Type -> t
let any_qn = ["PatternMatching"; "__"]

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

(** β-reduce a term `tm`.
This is useful to remove needles function applications introduced by F*, like
``(fun a b c -> a) 1 2 3``. **)
let beta_reduce (tm: term) : Tac term =
  norm_term [] tm ()

(** Reduce then compile a term `tm` into a pattern.
The reduction phase ensures that the pattern looks reasonable; it is needed
because F* tends to infer arguments in β-expanded form. **)
let pattern_of_term tm : Tac pattern =
  admit ();
  lift_exn_tac pattern_of_term_ex (beta_reduce tm)

/// Pattern-matching problems
/// =========================

let debug msg : Tac unit = () // print msg ()

/// Definitions
/// -----------

let absvar : eqtype = admit(); binder // FIXME
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
      (List.Tot.map (fun (nm, pat) -> nm ^ ": " ^ (string_of_pattern pat)) mp.mp_hyps) in
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
      (List.Tot.map (fun (varname, tm) -> varname ^ ": " ^ (term_to_string tm)) ms.ms_vars) in
  let hyps =
    String.concat "\n        "
      (List.Tot.map (fun (nm, binder) -> nm ^ ": " ^ (inspect_bv binder)) ms.ms_hyps) in
  "\n{ vars: " ^ vars ^ "\n" ^
  "  hyps: " ^ hyps ^ " }"

/// Notations
/// ---------

let var (a: Type) = a
let hyp (a: Type) = binder
let goal (a: Type) = unit

let var_qn = ["PatternMatching"; "var"]
let hyp_qn = ["PatternMatching"; "hyp"]
let goal_qn = ["PatternMatching"; "goal"]

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

// Must store this because recomputing it yields different names
type abspat_continuation =
  list abspat_argspec * term

let classify_abspat_binder binder : match_res (abspat_binder_kind * term) =
  admit ();
  let varname = "v" in
  let var_pat = PApp (PQn var_qn) (PVar varname) in
  let hyp_pat = PApp (PQn hyp_qn) (PVar varname) in
  let goal_pat = PApp (PQn goal_qn) (PVar varname) in

  let typ = type_of_binder binder in
  match interp_pattern var_pat typ with
  | Success [(_, var_typ)] -> Success (ABKVar var_typ, var_typ)
  | Failure _ ->
    match interp_pattern hyp_pat typ with
    | Success [(_, hyp_typ)] -> Success (ABKHyp, hyp_typ)
    | Failure _ ->
      match interp_pattern goal_pat typ with
      | Success [(_, goal_typ)] -> Success (ABKGoal, goal_typ)
      | Failure _ -> Failure IncorrectTypeInAbsPatBinder

(** Split an abstraction `tm` into a list of binders and a body. **)
let rec binders_and_body_of_abs tm : binders * term =
  match inspect tm with
  | Tv_Abs binder tm ->
    let binders, body = binders_and_body_of_abs tm in
    binder :: binders, body
  | _ -> [], tm

let unfold_vars (t: typ) : Tac typ =
  norm_term [delta_only ["PatternMatching.var"]] t ()

(** Parse a notation into a matching problem and a continuation.

Pattern-matching notations are of the form ``(fun binders… -> continuation)``,
where ``binders`` are of one of the forms ``var …``, ``hyp …``, or ``goal …``.
``var`` binders are typed holes to be used in other binders; ``hyp`` binders
indicate a pattern to be matched against hypotheses; and ``goal`` binders match
the goal.

The continuation returned can't directly be applied to a pattern-matching solution;
see ``interp_abspat_continuation`` below for that. **)
let matching_problem_of_abs (tm: term) : Tac (matching_problem * abspat_continuation) =
  admit ();

  let binders, body = binders_and_body_of_abs tm in
  debug ("Got binders: " ^ (String.concat ", " (List.Tot.map inspect_bv binders)));

  let problem =
    tacfold_left
      (fun problem (binder: binder) ->
         let bv_name = inspect_bv binder in
         debug ("Got binder: " ^ (inspect_bv binder));
         let binder_kind, typ = lift_exn_tac classify_abspat_binder binder in
         let typ_novars = unfold_vars typ in
         debug ("Compiling binder " ^ inspect_bv binder ^
                ", classified as " ^ string_of_abspat_binder_kind binder_kind ^
                ", with type " ^ term_to_string typ);
         match binder_kind with
         | ABKVar _ -> { problem with mp_vars = bv_name :: problem.mp_vars }
         | ABKHyp -> { problem with mp_hyps = (bv_name, (pattern_of_term typ_novars)) :: problem.mp_hyps }
         | ABKGoal -> { problem with mp_goal = Some (pattern_of_term typ_novars) })
      ({ mp_vars = []; mp_hyps = []; mp_goal = None })
      binders in

  let continuation =
    let abspat_argspec_of_binder binder : Tac abspat_argspec =
      let binder_kind, _ = lift_exn_tac classify_abspat_binder binder in
      { asa_name = binder; asa_kind = binder_kind } in
    (tacmap abspat_argspec_of_binder binders, tm) in

  let mp =
    { mp_vars = List.rev #varname problem.mp_vars;
      mp_hyps = List.rev #(varname * pattern) problem.mp_hyps;
      mp_goal = problem.mp_goal } in
  mp, continuation

/// Continuations
/// -------------

(** Get the (quoted) type expected by a specific kind of abspat binder **)
let arg_type_of_binder_kind binder_kind : Tac term =
  match binder_kind with
  | ABKVar typ -> typ
  | ABKHyp -> quote binder ()
  | ABKGoal -> quote unit ()

(** Find a varname in an association list; fail if it can't be found **)
let assoc_varname_fail (#b: Type) (key: varname) (ls: list (varname * b)) : Tac b =
  match List.Tot.assoc key ls with
  | None -> fail ("Not found: " ^ key) ()
  | Some x -> x

// FIXME simplify this instead of applying the continuations directly

let ms_locate_hyp (a: Type) (solution: matching_solution)
                  (name: varname) : Tac binder =
  assoc_varname_fail name solution.ms_hyps

let ms_locate_var (a: Type) (solution: matching_solution)
                  (name: varname) : Tac a =
  admit ();
  unquote #a (assoc_varname_fail name solution.ms_vars) ()

let ms_locate_unit (a: Type) _solution _binder_name : Tac unit =
  ()

let locate_fn_of_binder_kind binder_kind =
  match binder_kind with
  | ABKVar _ -> quote_lid ["PatternMatching"; "ms_locate_var"] ()
  | ABKHyp -> quote_lid ["PatternMatching"; "ms_locate_hyp"] ()
  | ABKGoal -> quote_lid ["PatternMatching"; "ms_locate_unit"] ()

let abspat_arg_of_abspat_argspec solution_term (argspec: abspat_argspec)
    : Tac term =
  admit ();
  let loc_fn = locate_fn_of_binder_kind argspec.asa_kind in
  let name_tm = pack (Tv_Const (C_String (inspect_bv argspec.asa_name))) in
  let locate_args = [(arg_type_of_binder_kind argspec.asa_kind, Q_Explicit);
                     (solution_term, Q_Explicit); (name_tm, Q_Explicit)] in
  mk_app loc_fn locate_args

let specialize_abspat_continuation' (continuation: abspat_continuation)
    : Tot (solution_term:term -> Tac term) =
  admit ();
  fun solution_term ->
    let mk_arg argspec =
      (abspat_arg_of_abspat_argspec solution_term argspec, Q_Explicit) in
    let argspecs, body = continuation in
    mk_app body (tacmap mk_arg argspecs)

let specialize_abspat_continuation (continuation: abspat_continuation)
    : Tac term =
  admit ();
  let solution_binder = fresh_binder (quote matching_solution ()) in
  let solution_term = pack (Tv_Var solution_binder) in
  let applied = specialize_abspat_continuation' continuation solution_term in
  let thunked = pack (Tv_Abs solution_binder applied) in
  debug ("Specialized into " ^ (term_to_string thunked));
  let normalized = beta_reduce thunked in
  debug ("… which reduces to " ^ (term_to_string normalized));
  normalized

let interp_abspat_continuation a (continuation: abspat_continuation)
    : Tac (matching_solution -> Tac a) =
  admit ();
  let applied = specialize_abspat_continuation continuation in
  unquote #(matching_solution -> Tac a) applied ()

let tinterp_abspat_continuation a (continuation: abspat_continuation)
    : Tac (matching_solution -> tactic a) =
  admit ();
  let applied = specialize_abspat_continuation continuation in
  unquote #(matching_solution -> tactic a) applied ()

/// Resolution
/// ----------

// FIXME handle multiple goal patterns

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
    fail #a "No matching hypothesis" ()
  | h :: hs ->
    or_else // Must be in ``Tac`` here to run `body`
      (fun () ->
         match interp_pattern_aux pat part_sol.ms_vars (type_of_binder h) with
         | Failure ex ->
           fail ("Failed to match hyp: " ^ (string_of_match_exception ex)) ()
         | Success bindings ->
           let ms_hyps = (name, h) :: part_sol.ms_hyps in
           body ({ part_sol with ms_vars = bindings; ms_hyps = ms_hyps }))
      (fun () ->
         solve_mp_for_single_hyp name pat hs body part_sol)
      ()

(** Scan ``hypotheses`` for matches for ``mp_hyps`` that lets ``body`` succeed. **)
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
      | Failure ex -> fail ("Failed to match goal: " ^ (string_of_match_exception ex)) ()
      | Success bindings -> { ms_vars = bindings; ms_hyps = [] } in
  solve_mp_for_hyps #a problem.mp_hyps hypotheses body goal_ps

/// Binding solutions
/// -----------------

#set-options "--print_bound_var_types --print_full_names --print_implicits" // --ugly

let fff =
  fun (solution: matching_solution) ->
   (fun (a:var Type0) ->
   (fun (b:var Type0) ->
   (fun (h1:hyp (a ==> b)) ->
   (fun (h2:hyp a) ->
   (fun (uu___938073:goal (Prims.squash b)) ->
     print "AA" ()
     ) (ms_locate_unit (Prims.squash b) solution "uu___#937590")
     ) (ms_locate_hyp a solution "h2#937588")
     ) (ms_locate_hyp (a ==> b) solution "h1#937585")
     ) (ms_locate_var Type0 solution "b#937581")
     ) (ms_locate_var Type0 solution "a#937576")

// let xxxx () : Tot unit =
//   assert_by_tactic True
//                    (let open FStar.Tactics in
//                     print "0";;
//                     abs  <--  quote (fun (a b: var Type0) (h1: hyp (a ==> b)) (h2: hyp (a)) (_: goal (squash b)) ->
//                                    print "AA" ());
//                     print "1";;
//                     pc  <--  (fun () -> matching_problem_of_abs abs);
//                     print "2";;
//                     let problem, continuation = pc in
//                     print "2b";;
//                     _k <-- (fun () -> interp_abspat_continuation unit continuation);
//                     print "3")

/// Examples
/// --------

open FStar.Tactics

// let mp_example : matching_problem =
//   synth_by_tactic
//     (fun () ->
//       let abs = quote (fun (a b: Type) (h1: hyp (a ==> b)) (h2: hyp (a)) (_: goal (squash b)) ->
//                          let open FStar.Tactics in
//                          print (inspect_bv h1);;
//                          print (inspect_bv h2)) () in
//       let mp, continuation = matching_problem_of_abs abs in
//       // let qq = quote mp () in
//       // print_term qq ();
//       exact (quote mp) ())

// let print_binders abs : Tac unit =
//   let bdtm = binders_and_body_of_abs abs in
//   let binders, tm = bdtm in
//   print (String.concat ", " (List.Tot.map inspect_bv binders)) ()

let interp_abspat #a (abspat: a) : Tac (matching_problem * abspat_continuation) =
  admit ();
  let abs = quote abspat () in
  matching_problem_of_abs abs

let match_abspat #b #a (abspat: a)
                 (k: abspat_continuation -> Tac (matching_solution -> Tac b))
    : Tac b =
  admit ();
  let goal = cur_goal () in
  let hypotheses = binders_of_env (cur_env ()) in
  let problem, continuation = interp_abspat abspat in
  solve_mp #matching_solution problem hypotheses goal (k continuation)

let inspect_abspat_problem #a (abspat: a) : Tac matching_problem =
  fst (interp_abspat #a abspat)

let inspect_abspat_solution #a (abspat: a) : Tac matching_solution =
  admit ();
  match_abspat abspat (fun _ -> (fun solution -> solution) <: Tac _)

#set-options "--admit_smt_queries true"
let tpair #a #b : a -> Tac (b -> Tac (a * b)) =
  fun (x: a) -> (fun (y: b) -> (x, y) <: Tac _) <: Tac _
#reset-options

let lpm #b #a (abspat: a) : tactic b =
  admit ();
  fun () ->
    let continuation, solution = match_abspat abspat tpair in
    interp_abspat_continuation b continuation solution

let tlpm #b #a (abspat: a) : tactic b =
  admit ();
  fun () ->
    let continuation, solution = match_abspat abspat tpair in
    tinterp_abspat_continuation b continuation solution

let pm (#b: Type u#0) (#a: Type u#1) (abspat: a) : tactic b =
  admit ();
  fun () ->
    match_abspat abspat (interp_abspat_continuation b)

let rec first #a (tacs: list (tactic a)) : Tac a (decreases tacs) =
  match tacs with
  | [] -> fail #a "All tactics failed" ()
  | t1 :: tacs -> match trytac t1 () with
                | Some r -> r
                | None -> first tacs

let tfirst #a (tacs: list (tactic a)) : tactic a =
  fun () -> first tacs

let unsquash #a : a -> squash a =
  fun _ -> ()

let split_hd #a #b #c (pr: a -> b -> c) : (a `c_and` b -> c) =
  function (Prims.And a b) -> pr a b

// #set-options "--print_bound_var_types --print_full_names --print_implicits --print_effect_args" // --ugly

// let split_hyp_lemma #a #b #c : Lemma (a `c_and` b -> c) =
//   assert_by_tactic (a `c_and` b -> c)
//                    (apply (quote (unsquash #(a `c_and` b -> c)));;
//                     dump "BB";;
//                     apply (quote (split_hd #a #b #c));;
//                     _ <-- intros;
//                     dump "CC")

let ignore #a (x: a) : Tot unit = ()

let implies_intro' : tactic unit =
  _ <-- implies_intro; return ()

let repeat' #a (f: tactic a) : tactic unit =
  _ <-- repeat f; return ()

let and_elim' (h: binder) : tactic unit =
  and_elim (pack (Tv_Var h));;
  clear h

let exact_hyp (a: Type0) (h: binder) : tactic unit =
  hd <-- quote (FStar.Squash.return_squash #a);
  exact (return (mk_app hd [((pack (Tv_Var h)), Q_Explicit)]))
  // apply (quote (FStar.Squash.return_squash #a));;
  // exact (return (pack (Tv_Var h)))

let mustfail #a (t: tactic a) (message: string) : tactic unit =
  fun () ->
    match trytac t () with
    | Some _ -> fail message ()
    | None -> ()

let done : tactic unit =
  mustfail cur_goal "Some goals are left"

#set-options "--admit_smt_queries true"

let example #a #b #c: unit =
  assert_by_tactic (a /\ b ==> c == b ==> c)
                   (repeat' // FIXME why does adding #unit here fail?
                     (idtac;; // FIXME: removing this ``idtac`` makes everything fail, really slowly
                      lpm #unit (fun (a: var Type) (h: hyp (squash a)) ->
                             clear h ())
                      `or_else`
                      lpm #unit (fun (a b: var Type0) (_: goal (squash (a ==> b))) ->
                             implies_intro' () <: Tac unit)
                      `or_else`
                      lpm #unit (fun (a b: var Type0) (h: hyp (a /\ b)) ->
                             and_elim' h () <: Tac unit)
                      `or_else`
                      lpm #unit (fun (a b: var Type0) (h: hyp (a == b)) (_: goal (squash a)) ->
                             rewrite h () <: Tac unit)
                      `or_else`
                      lpm #unit (fun (a: var Type0) (h: hyp a) (_: goal (squash a)) ->
                                   exact_hyp a h () <: Tac unit));;
                    done)

let example #a #b #c: unit =
  assert_by_tactic (a /\ b ==> c == b ==> c)
                   (tfirst #unit
                      [lpm (fun (a: var Type) (h: hyp (squash a)) ->
                              clear h () <: Tac unit);
                       lpm (fun (a b: var Type0) (_: goal (squash (a ==> b))) ->
                              implies_intro' () <: Tac unit);
                       lpm (fun (a b: var Type0) (h: hyp (a /\ b)) ->
                              and_elim' h () <: Tac unit);
                       lpm (fun (a b: var Type0) (h: hyp (a == b)) (_: goal (squash a)) ->
                              rewrite h () <: Tac unit);
                       lpm (fun (a: var Type0) (h: hyp a) (_: goal (squash a)) ->
                              exact_hyp a h () <: Tac unit)];;
                    done)

// let example (a b: int) =
//   assert_by_tactic (a == b ==> a + 1 == b + 1)
//                    (_ <-- implies_intro;
//                     ms <-- (fun () -> inspect_abspat_solution
//                            (fun (a b: var int) (h: hyp (a == b)) -> rewrite h));
//                     print "AAA";;
//                     print (string_of_matching_solution ms);;
//                     // print (string_of_matching_problem mp);;
//                     fail "A")

let example (a b: int) =
  assert_by_tactic (a == b ==> a + 1 == b + 1)
                   (_ <-- implies_intros;
                    env <-- cur_env;
                    dump "AA";;
                    let binders = binders_of_env env in
                    print (String.concat "\n\n" (List.Tot.map (fun b -> inspect_bv b ^ ": " ^ (term_to_string (type_of_binder b))) binders));;
                    match List.Tot.rev binders with
                    | [] -> print "??"
                    | h :: _ ->
                      rewrite h;;
                      dump "BB")


let example (p1 p2: Type0) =
  assert_by_tactic (p1 ==> (p1 ==> p2) ==> p2)
                   (_ <-- implies_intros;
                    env <-- cur_env;
                    dump "AA";;
                    let binders = binders_of_env env in
                    print (String.concat "\n\n" (List.Tot.map (fun b -> inspect_bv b ^ ": " ^ (term_to_string (type_of_binder b))) binders));;
                    match List.Tot.rev binders with
                    | [] -> print "??"
                    | h :: _ ->
                      let t = pack (Tv_Var h) in
                      apply_lemma (return t))
                    // mgw unit (fun (a b: var) (h1: hyp (a ==> b)) (h2: hyp (a)) (_: goal (squash b)) ->
                    //             let open FStar.Tactics in
                    //             print "hello!" ();
                    //             print (inspect_bv h1) ();
                    //             print (inspect_bv h2) ();
                    //             apply_lemma (fun () -> (pack (Tv_Var h1))) ())

// let __ =
//   assert_by_tactic (1 == 1)
//                    (fun () ->
//                      let problem = { )

//   hyp_binders <--

let tmatch_term pat tm : tactic bindings =
  lift_exn_tactic (interp_pattern pat) tm

let tmatch_goal pat : tactic bindings =
  let open FStar.Tactics in
  cg <-- cur_goal;
  tmatch_term pat cg

// let pat : pattern =
//   synth_by_tactic (abspat (fun (x: int) -> x == x))

let pat = (PApp (PApp (PApp (PQn ["Prims"; "eq2"])
                               (PQn ["Prims"; "int"]))
                        (PVar "x"))
                 (PVar "x"))

open FStar.Tactics

#set-options "--tactic_trace"

let string_of_res res =
  match res with
  | Success bb -> "OK"
  | Failure ex -> (string_of_match_exception ex)

// Beta reduction not working
let test () =
  assert_by_tactic (1 == 1)
    (fun () ->
      let pat = abspat' (fun (x: int) -> Prims.squash (x == x)) in
      let bindings = match_goal pat in
      print (string_of_bindings bindings) ();
      trefl ())

// let (%) #a (h: unit) (y: Type) =
//   unit

// mgw
//   [(fun a b | (h1: a) (h2: a -> b) (goal: b) -> pose proof (h1 h2));
//    (fun a b (h: a /\ b) -> split h)]


let pattern_of_abspat abspat =
  abspat_term <-- quote abspat;
  pat <-- lift_exn_tac pattern_of_abs abspat_term;
  return pat

let match_goal_with abspat =
  pat <-- pattern_of_abspat abspat;
  match_goal_with_pat pat

let match_term_with abspat tm =
  pat <-- pattern_of_abspat abspat;
  match_term_with_PatternMatching pat tm

// bindings <-- match_goal_with_pat (PApp (PQn squash_qna) [PApp (PQn eq2_qn) [PAny; PVar "a"; PVar "b"]]);

// Ltac reflect term :=
//   lazymatch term with
//   | op ?x ?y -> =
//     let rx := reflect x in
//     let ry := reflect y in
//     constr:(Node rx ry)
//   | _ -> constr:(Leaf term)

// let unquote #a tm : a =
//   synth_by_tactic (exact (return tm))

let match_term_with2 (tm: term) (abspat: 'a -> 'b -> 'c) (k: term -> term -> tactic 'd) : tactic 'd =
  pat <-- pattern_of_abspat abspat;
  bindings <-- match_term pat tm;
  match bindings with
  | [(_, t1); (_, t2)] -> k t1 t2
  | _ -> fail ("Too many or too few bindings: " ^ (string_of_bindings bindings))

let match_goal_with2 (abspat: 'a -> 'b -> 'c) (k: term -> term -> tactic 'd) : tactic 'd =
  g <-- cur_goal;
  match_term_with2 g abspat k

let print_pattern (abspat: 'a) : tactic unit =
  pat <-- pattern_of_abspat abspat;
  print (string_of_PatternMatching pat)

assume val a0: a
assume val a0_neutral_l : a1: a -> Lemma ((a1 `op` a0) `eql` a1)
assume val a0_neutral_r : a1: a -> Lemma ((a0 `op` a1) `eql` a1)
assume val op_comm : a1: a -> a2: a -> Lemma ((a1 `op` a2) `eql` (a2 `op` a1))
assume val op_PatternMatching : a1: a -> a2: a -> Lemma ((a1 `op` a1) `eql` (a2 `op` a2))

let rec first #a (tactics: list (tactic a)) : tactic a =
  match tactics with
  | [] -> fail "No tactics"
  | [t] -> t
  | t :: ts -> or_else t (first ts)

let ( --> ) abspat tac =
  match_goal_with abspat;;
  tac

// TODO: Add a forall handler

let string_of_binder (b: binder) =
  term_to_string (type_of_binder b)

let match_env_with abspat =
  env <-- cur_env;
  let hyps = binders_of_env env in
  print_pattern abspat;;
  let matcher = match_term_with abspat in
  first (List.Tot.map (fun hyp ->
             bindings <-- matcher (type_of_binder hyp);
             return (hyp, bindings))
           hyps)

// let reif tm : tactic unit =
//   bindings <-- match_term_with (fun x -> - x) tm;
//   match bindings with
//   | [(_, tx)] -> print_term tx;;
//                 idtac
//   | _ -> fail "A"

// let x () : Lemma True =
//   assert_by_tactic True
//     (m1 <-- quote (- 1);
//      reif m1)

let rec reflect_ops (tm: term) : tactic term =
  or_else (match_term_with2 tm (fun x y -> x `op` y)
             (fun x y -> admit ();
                      rx <-- reflect_ops x;
                      ry <-- reflect_ops y;
                      node <-- quote Node;
                      return (mk_app node [rx; ry])))
          (leaf <-- quote Leaf;
           return (mk_app leaf [tm]))


// assume val g1: Type0
// assume val g2: Type0
// assume val w1: g1
// assume val w12: g1 -> g2

// let test : unit =
//   assert_by_tactic g2 (apply (quote w12);; exact (quote w1))

let change_goal_lemma (#g1 #g2: Type0) : squash g1 -> (squash (g1 == g2)) -> squash g2 =
  (fun w1 eq -> w1)

// let prove_assoc (a1 a2 a3: a) : Lemma True =
//   assert_by_tactic (a1 `eql` a2)
//     (apply (quote (change_goal_lemma #(a1 `eql` a2) #(a1 `eql` a2)));;
//      idtac)

// let prove_assoc (a1 a2 a3: a) : Lemma True =
//   // assert_by_tactic ((a1 `op` (a2 `op` a3)) `eql` ((a1 `op` a2) `op` a3))
//   assert_by_tactic (a1 `eql` a2)
//     (xy <-- match_goal_with (fun x y -> squash (x `eql` y));
//      match xy with
//      | [(_, tx); (_, ty)] ->
//        dup;;
//        eq_fv <-- quote eql;
//        squash_fv <-- quote squash;
//        aa1 <-- quote a1;
//        aa2 <-- quote a2;
//        exact (return (mk_app squash_fv [mk_app eq_fv [aa1; aa2]]));;
//        trefl
//      | _ -> fail "impossible")


// FIXME why does running fail on 0 goals fail?
// FIXME does bind apply tactics to each goal individually?

// let weaken hyp impl =

// let test0 (f: False \/ False) : Lemma True =
//   assert_by_tactic False (res <-- match_env_with (fun x y -> x \/ y);
//                       print (string_of_bindings (snd res));;
//                       fail "A")

type narg_type = name:string * typ:Type
type narg #t: Type = name:string * value:t

noeq type klist : (ts: list narg_type) -> Type =
| HNil: klist []
| HCons: #hdT:Type -> #tlT: list narg_type ->
         hd:(string * hdT) ->
         tl:(klist tlT) ->
         klist ((fst hd, hdT) :: tlT)

type kfunc (nargTs: list narg_type) retT =
  klist nargTs -> retT

let (^.) = HCons

let x = ("start", 1) ^. ("len", 2) ^. ("str", "abc") ^. HNil


let bind_bind_t
    (m: Type -> Type)
    (return: #a: Type -> aa: a -> m a)
    (bind: #a: Type -> #b: Type -> m a -> (a -> m b) -> m b) =
  forall #a #b #c (ma: m a) (f: a -> m b) (g: b -> m c).
     bind #b #c (bind ma f) g ==
     bind #a #c ma (fun (aa: a) -> bind (f aa) g)

noeq type monad_typeclass =
| MkMonad :
    m: (Type -> Type) ->
    return: (#a:Type -> aa: a -> m a) ->
    bind: (#a: Type -> #b: Type -> m a -> (a -> m b) -> m b) ->
    bind_bind: (forall #a #b #c (ma: m a) (f: a -> m b) (g: b -> m c).
                bind #b #c (bind ma f) g ==
                bind #a #c ma (fun (aa: a) -> bind (f aa) g)) ->
    monad_typeclass



assume val substring: s:string -> start:int -> len:int -> string

// match_term #(#x + #y) #(return (#x - #y)) { x=1; y=2 }

let ex_capture : unit =
  assert_by_tactic (True \/ False)
    (bindings <-- match_goal_with (fun x y -> squash (x \/ y));
     print (string_of_bindings bindings))

let ex_non_linear_mismatch : unit =
  assert_by_tactic (True \/ False)
    (match_goal_with (fun x -> squash (x \/ __));;
     idtac)


let step =
  first [True
           --> trivial;

         squash (__ /\ __)
           --> split;

         (fun x y -> squash ((x `op` y) `eql` (y `op` x)))
           --> apply_lemma (quote op_comm);

         (fun x y -> squash ((x `op` x) `eql` (y `op` y)))
           --> apply_lemma (quote op_same_squares);

         fail "Nope"]

let crush =
  repeat step;; idtac
  // or_else trivial (fail "crush failed")

let ex0 (a1 a2: a) =
  assert_by_tactic ((a1 `op` a2) `eql` (a2 `op` a1)) crush

let ex1 (a1 a2: a) =
  assert_by_tactic ((a1 `op` a1) `eql` (a2 `op` a2)) crush

let ex2 (a1 a2: a) =
  assert_by_tactic (((a1 `op` a1) `eql` (a2 `op` a2)) /\ True) crush

let ex2 (a1 a2: a) =
  assert_by_tactic ((((a1 `op` a1) `eql` (a2 `op` a2)) /\ True)) crush

let ex_non_linear_mismatch : unit =
  assert_by_tactic (True \/ False)
    (match_goal_with (fun x -> squash (x \/ x));;
     idtac)

















let test2 (a1 a2 a3 a4 a5 a6 a7: a)
    : Lemma ((a1 `op` (a2 `op` a3)) `op` (((a4 `op` a5) `op` a6) `op` a7) `eql`
             (a1 `op` (a2 `op` (a3 `op` (((a4 `op` a5) `op` a6) `op` a7))))) =
  assert_by_tactic ((a1 `op` (a2 `op` a3)) `op` (((a4 `op` a5) `op` a6) `op` a7) `eql`
                    (a1 `op` (a2 `op` (a3 `op` (((a4 `op` a5) `op` a6) `op` a7)))))
                   (dump "A";;
                    xx <-- print_pattern (fun (x y: a) -> squash (x `eql` x));
                    match_goal_with2 (fun (x y: a) -> squash (x `eql` x))
                         (fun (x y: term) -> print_term x;; print_term y);;
                    fail "A");
  admit ()

// Ltac reflect term :=
//   lazymatch term with
//   | op ?x ?y -> =
//     let rx := reflect x in
//     let ry := reflect y in
//     constr:(Node rx ry)
//   | _ -> constr:(Leaf term)

// Ltac subst_reflected term :=
//   let reflected := reflect term in
//   change term with (interp reflected);
//   rewrite !(interp_flatten reflected).

// Ltac solve_eq :=
//   lazymatch goal with
//   | [  |- ?x = ?y ] ->
//     subst_reflected x;
//     subst_reflected y;
//     reflexivity

// Ltac solve_eq_slow := rewrite !Opassoc; reflexivity.

// let rec balanced n a =
//   match n with
//   | O -> a
//   | S x -> Op (Balanced x a) (Balanced x a)

// let rec pow2 n =
//   match n with
//   | O -> 1
//   | S x -> (pow2 x) + (pow2 x)

// let rec skewed n a =
//   match n with
//   | O -> a
//   | S x -> Op a (Skewed x a)

// Definition eqN n := forall a, Balanced n a = Skewed (pow2 n - 1) a.

// Goal eqN 7.
//   intro; simpl.
//   Time solve_eq_slow.
// Qed.


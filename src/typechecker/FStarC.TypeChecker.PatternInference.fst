module FStarC.TypeChecker.PatternInference

open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Class.Setlike
open FStarC.Class.Show

module S    = FStarC.Syntax.Syntax
module SS   = FStarC.Syntax.Subst
module U    = FStarC.Syntax.Util
module Free = FStarC.Syntax.Free
module Env  = FStarC.TypeChecker.Env
module PC   = FStarC.Parser.Const

(* Import showable instances for terms *)
open FStarC.Syntax.Print

(* Check if a term is eligible to appear inside an SMT pattern.
   Must contain only function applications, constants, and variables.
   Must not contain smt_theory_symbol functions, binders, or lets.
   The head of a Tm_app must be a top-level function (Tm_fvar), not
   a local variable — applications of local variables create unstable patterns. *)
let rec is_pattern_eligible (env:Env.env) (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_name _
  | Tm_bvar _
  | Tm_constant _
  | Tm_type _ -> true

  | Tm_fvar fv ->
    not (Env.fv_has_attr env fv PC.smt_theory_symbol_attr_lid)

  | Tm_uinst (t, _) ->
    is_pattern_eligible env t

  | Tm_app {hd; args} ->
    is_head_fvar hd &&
    is_head_non_recursive env hd &&
    is_pattern_eligible env hd &&
    List.for_all (fun (a, _) -> is_pattern_eligible env a) args

  | _ -> false

(* Check that the head of an application is a top-level function (Tm_fvar),
   not a local variable (Tm_name). Applications of local variables like
   (p x) where p is a function parameter create unstable SMT patterns.
   Also rejects recursive functions — patterns on recursive calls
   cause matching loops (e.g., calc_chain_related). *)
and is_head_fvar (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_fvar _ -> true
  | Tm_uinst (t, _) -> is_head_fvar t
  | _ -> false

and is_head_non_recursive (env:Env.env) (t:term) : ML bool =
  match (SS.compress t).n with
  | Tm_fvar fv ->
    begin match Env.lookup_qname env fv.fv_name with
    | Some (Inr ({sigel = Sig_let {lbs=(is_rec, _)}}, _), _) -> not is_rec
    | Some (Inl _, _) ->
      (* In-scope binding (e.g., letrec being defined) — conservative: treat as recursive *)
      false
    | _ -> true  (* not a let-binding (e.g., val, assume), fine *)
    end
  | Tm_uinst (t, _) -> is_head_non_recursive env t
  | _ -> true

(* Collect candidate pattern terms from a quantifier body.
   Returns pairs of (candidate_term, list of covered quantifier bvs).
   Does not descend into nested binders (abs, let, nested quantifiers).
   Uses a greedy approach: only adds a parent Tm_app if no child
   covers the same or more quantifier variables. *)
let rec collect_candidates (env:Env.env) (qvars:list bv) (t:term)
  : ML (list (term & list bv))
=
  let t = SS.compress t in
  match t.n with
  (* Stop at binders — don't look inside *)
  | Tm_abs _
  | Tm_let _ -> []

  | Tm_app {hd; args} ->
    let head = U.un_uinst hd in
    begin match head.n with
    (* Stop at nested quantifiers *)
    | Tm_fvar fv when U.is_qlid fv.fv_name -> []
    | _ ->
      (* First collect candidates from children *)
      let child_candidates =
        List.collect (fun (a, _) -> collect_candidates env qvars a) args @
        collect_candidates env qvars hd
      in
      (* Check if this entire Tm_app is pattern-eligible *)
      if is_pattern_eligible env t then
        let free_bvs = Free.names t in
        let covered = List.filter (fun qv -> mem qv free_bvs) qvars in
        if List.length covered > 0 then
          (* Only add self if no child covers the same or more vars *)
          let dominated_by_child =
            List.existsb (fun (_, child_covered) ->
              List.for_all (fun cv ->
                List.existsb (fun ccv -> S.bv_eq cv ccv) child_covered
              ) covered
            ) child_candidates
          in
          if dominated_by_child
          then child_candidates
          else (t, covered) :: child_candidates
        else child_candidates
      else child_candidates
    end

  | Tm_meta {tm} -> collect_candidates env qvars tm
  | Tm_ascribed {tm} -> collect_candidates env qvars tm
  | _ -> []

(* Collect binders from nested quantifier applications.
   Descends through Tm_app(forall/exists, [Tm_abs{bs=[b]; body=...}]).
   Returns (binders in reverse order, innermost body). *)
let rec collect_quantifier_binders (t:term) (acc:list binder)
  : ML (list binder & term)
=
  let t = SS.compress t in
  let head, args = U.head_and_args t in
  match (U.un_uinst head).n with
  | Tm_fvar fv when U.is_qlid fv.fv_name ->
    begin match args with
    | [(arg, _)]
    | [_; (arg, _)] ->
      begin match (SS.compress arg).n with
      | Tm_abs {bs=[b]; body} ->
        collect_quantifier_binders body (b :: acc)
      | _ -> (acc, t)
      end
    | _ -> (acc, t)
    end
  | _ -> (acc, t)

(* Replace the innermost body in a nested quantifier structure,
   descending n levels deep through the Tm_app/Tm_abs chain. *)
let rec replace_innermost (t:term) (n:int) (new_body:term) : ML term =
  if n = 0 then new_body
  else
    let t = SS.compress t in
    let head, args = U.head_and_args t in
    match args with
    | [(arg, q)] ->
      begin match (SS.compress arg).n with
      | Tm_abs {bs=[b]; body; rc_opt} ->
        let new_inner = replace_innermost body (n-1) new_body in
        let new_abs = S.mk (Tm_abs {bs=[b]; body=new_inner; rc_opt}) arg.pos in
        S.mk (Tm_app {hd=head; args=[(new_abs, q)]}) t.pos
      | _ -> t
      end
    | [type_arg; (arg, q)] ->
      begin match (SS.compress arg).n with
      | Tm_abs {bs=[b]; body; rc_opt} ->
        let new_inner = replace_innermost body (n-1) new_body in
        let new_abs = S.mk (Tm_abs {bs=[b]; body=new_inner; rc_opt}) arg.pos in
        S.mk (Tm_app {hd=head; args=[type_arg; (new_abs, q)]}) t.pos
      | _ -> t
      end
    | _ -> t

(* Main entry point: attempt to infer patterns for a quantifier application.
   Detects forall/exists head, descends to innermost body, checks for
   existing patterns, and infers if none present. *)
let maybe_infer_patterns (env:Env.env) (t:term) : ML term =
  let head, _ = U.head_and_args t in
  match (U.un_uinst head).n with
  | Tm_fvar fv when U.is_qlid fv.fv_name ->
    (* Collect all binders from nested quantifiers *)
    let rev_binders, innermost = collect_quantifier_binders t [] in
    let binders = List.rev rev_binders in
    if List.length binders = 0 then t
    else

    (* Check innermost body for existing patterns *)
    let innermost_c = SS.compress innermost in
    let has_user_pattern, body_under_meta =
      match innermost_c.n with
      | Tm_meta {tm; meta=Meta_pattern(_, pats)} ->
        (List.length pats > 0, tm)
      | _ -> (false, innermost)
    in
    if has_user_pattern then t
    else

    (* Open all binders to get proper Tm_name references *)
    let bs_opened, body_opened = SS.open_term binders body_under_meta in
    let qvars = List.map (fun (b:binder) -> b.binder_bv) bs_opened in

    (* Collect and filter candidates *)
    let candidates = collect_candidates env qvars body_opened in

    let full_coverage = List.filter (fun (_, covered) ->
      List.for_all (fun qv ->
        List.existsb (fun cv -> S.bv_eq qv cv) covered
      ) qvars
    ) candidates in

    begin match full_coverage with
    | [] ->
      (* Inference failed — emit warning with reason *)
      let qvar_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) qvars in
      let qvar_str = String.concat ", " qvar_names in
      let reason =
        if List.length candidates = 0 then
          "no eligible candidate terms found in the quantifier body"
        else
          let uncovered = List.filter (fun qv ->
            not (List.existsb (fun (_, covered) ->
              List.existsb (fun cv -> S.bv_eq qv cv) covered
            ) candidates)
          ) qvars in
          if List.length uncovered > 0 then
            let uncovered_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) uncovered in
            Format.fmt1 "no candidate term mentions variable(s): %s"
                   (String.concat ", " uncovered_names)
          else
            "no single candidate term covers all bound variables (would need a conjunctive pattern)"
      in
      FStarC.Errors.log_issue t FStarC.Errors.Warning_SMTPatternIllFormed
        (Format.fmt2 "Could not automatically infer a pattern for quantifier over {%s}: %s" qvar_str reason);
      t

    | patterns ->
      (* Success: optionally report under --ext auto_patterns_diag *)
      if Options.Ext.enabled "auto_patterns_diag" then begin
        let qvar_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) qvars in
        let qvar_str = String.concat ", " qvar_names in
        let pat_strs = List.map (fun (t, _) -> show t) patterns in
        let pat_str = String.concat " \\/ " pat_strs in
        FStarC.Errors.info t
          (Format.fmt2 "Auto-pattern: for quantifier over {%s}, inferred {:pattern %s}" qvar_str pat_str)
      end;
      (* Build disjunctive pattern: each candidate becomes one disjunct *)
      let names = List.map S.bv_to_name qvars in
      let pats = List.map (fun (pat_term, _) -> [(pat_term, None)]) patterns in
      let new_meta_body =
        S.mk (Tm_meta {tm=body_opened; meta=Meta_pattern(names, pats)}) body_opened.pos
      in
      (* Close the binders back to de Bruijn form *)
      let new_body_closed = SS.close bs_opened new_meta_body in
      (* Replace the innermost body in the original term structure *)
      replace_innermost t (List.length binders) new_body_closed
    end

  | _ -> t

(* Infer patterns at the Meta_pattern level.
   Called when processing Tm_meta{Meta_pattern(names, [])}.
   `names` are Tm_name terms for the quantifier-bound variables.
   `body` is the typechecked quantifier body.
   Returns inferred patterns as list of disjuncts, or empty list on failure. *)
let infer_patterns_for_meta (env:Env.env) (names:list term) (body:term) : ML (list (list arg)) =
  (* Extract bvs from name terms *)
  let qvars = List.collect (fun t ->
    match (SS.compress t).n with
    | Tm_name bv -> [bv]
    | _ -> []
  ) names in
  if List.length qvars = 0 then []
  else
  let qvar_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) qvars in
  let qvar_str = String.concat ", " qvar_names in
  (* Collect and filter candidates *)
  let candidates = collect_candidates env qvars body in
  let full_coverage = List.filter (fun (_, covered) ->
    List.for_all (fun qv ->
      List.existsb (fun cv -> S.bv_eq qv cv) covered
    ) qvars
  ) candidates in
  match full_coverage with
  | [] ->
    (* Build a diagnostic message explaining WHY inference failed *)
    let reason =
      if List.length candidates = 0 then
        "no eligible candidate terms found in the quantifier body. " ^
        "Eligible terms must be function applications (f x) where f is a " ^
        "top-level function without the [@@smt_theory_symbol] attribute. " ^
        "The search does not descend into nested binders (let, fun, forall, exists)."
      else
        (* We have candidates but none cover all variables *)
        let partial_coverage = List.map (fun (t, covered) ->
          let covered_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) covered in
          Format.fmt2 "%s covers {%s}" (show t) (String.concat ", " covered_names)
        ) candidates in
        let uncovered = List.filter (fun qv ->
          not (List.existsb (fun (_, covered) ->
            List.existsb (fun cv -> S.bv_eq qv cv) covered
          ) candidates)
        ) qvars in
        let uncovered_names = List.map (fun (bv:bv) -> FStarC.Ident.string_of_id bv.ppname) uncovered in
        if List.length uncovered > 0 then
          Format.fmt2 "no candidate term mentions the bound variable(s): %s. Candidates found: %s"
                 (String.concat ", " uncovered_names)
                 (String.concat "; " partial_coverage)
        else
          Format.fmt2 "no single candidate term covers all bound variables (would need a conjunctive pattern across {%s}). Candidates found: %s"
                 qvar_str
                 (String.concat "; " partial_coverage)
    in
    FStarC.Errors.log_issue body FStarC.Errors.Warning_SMTPatternIllFormed
      (Format.fmt2 "Could not automatically infer a pattern for quantifier over {%s}: %s" qvar_str reason);
    []
  | patterns ->
    (* Success: optionally report under --ext auto_patterns_diag *)
    if Options.Ext.enabled "auto_patterns_diag" then begin
      let pat_strs = List.map (fun (t, _) -> show t) patterns in
      let pat_str = String.concat " \\/ " pat_strs in
      FStarC.Errors.info body
        (Format.fmt2 "Auto-pattern: for quantifier over {%s}, inferred {:pattern %s}" qvar_str pat_str)
    end;
    List.map (fun (pat_term, _) -> [(pat_term, None)]) patterns

(*
   Copyright 2025 Microsoft Research

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

(* The Pulse grammar, built on the F* grammar of
   FStarC.Parser.Grammar, which it extends in two ways:

   - the identifiers in [keywords] are keywords: the token stream is
     rewritten before parsing (see [rewrite_token]);

   - the type of a Pulse function, [fn (x:t) requires p ensures q], is a
     leading rule of F* terms, so it can be used in any type position.

   Statements and declarations are parsed by recursive descent. *)
module PulseSyntaxExtension.Grammar

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Ident
open FStarC.Parser.AST
open FStarC.Parser.Pratt
open FStarC.Parser.Grammar
open PulseSyntaxExtension.Sugar
module L  = FStarC.Parser.Lexer
module R  = FStarC.Range
module E  = FStarC.Errors
module S  = PulseSyntaxExtension.Sugar
module Pp = FStarC.Pprint
module Codes = FStarC.Errors.Codes

(* ---------------------------------------------------------------------- *)
(* Keywords                                                               *)
(* ---------------------------------------------------------------------- *)

let keywords : list (string & string) = [
  "mut", "MUT";
  "invariant", "INVARIANT";
  "predicate", "PREDICATE";
  "while", "WHILE";
  "fn", "FN";
  "divergent", "DIVERGENT";
  "each", "EACH";
  "rewrite", "REWRITE";
  "fold", "FOLD";
  "atomic", "ATOMIC";
  "ghost", "GHOST";
  "unobservable", "UNOBSERVABLE";
  "opens", "OPENS";
  "show_proof_state", "SHOW_PROOF_STATE";
  "norewrite", "NOREWRITE";
  "preserves", "PRESERVES";
  "goto", "GOTO";
  "label", "LABEL";
  "return", "RETURN";
  "continue", "CONTINUE";
  "break", "BREAK";
  "defer", "DEFER";
]

let rewrite_token (t:L.token) : ML L.token =
  if t.kind = "IDENT" then
    match FStar.List.Tot.assoc t.text keywords with
    | Some k -> { t with L.kind = k }
    | None -> t
  else t

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                *)
(* ---------------------------------------------------------------------- *)

let is_qual_kind (k:string) : bool =
  k = "GHOST" || k = "ATOMIC" || k = "UNOBSERVABLE" || k = "DIVERGENT"

(* qual *)
let p_qual (ps:pstate) : ML st_comp_tag =
  match (advance ps).kind with
  | "GHOST" -> STGhost
  | "ATOMIC" -> STAtomic
  | "UNOBSERVABLE" -> STUnobservable
  | "DIVERGENT" -> STDiv
  | _ -> backup ps 1; fail ps

(* qualOptFn *)
let qual_opt_fn (ps:pstate) : ML (option st_comp_tag) =
  let q = if is_qual_kind (peek_kind ps) then Some (p_qual ps) else None in
  ignore (expect ps "FN");
  q

let with_computation_tag (c:computation_type) (t:option st_comp_tag) : computation_type =
  match t with
  | None -> c
  | Some t -> { c with tag = t }

(* The local mk_fn_defn of pulseparser.mly *)
let mk_fn_defn' (q:option st_comp_tag) (id:ident) (is_rec:bool) (us:list ident) (bs:list binder)
    (body:either (computation_type & option term & stmt) (lambda & option term))
    (r:R.range) : fn_defn =
  match body with
  | Inl (ascription, measure, body) ->
    let ascription = with_computation_tag ascription q in
    S.mk_fn_defn id is_rec us bs (Inl ascription) measure (Inl body) [] r
  | Inr (lambda, typ) ->
    S.mk_fn_defn id is_rec us bs (Inr typ) None (Inr lambda) [] r

let p_appTermNoRecordExp (ps:pstate) : ML term = app_term ps true

(* tmNoEqWith(appTermNoRecordExp) *)
let p_tmNoEqNoRef (ps:pstate) : ML term = term_at ps noref_ctx 81

(* Statements end at a closing brace or parenthesis *)
let at_stmt_end (ps:pstate) : ML bool = is ps "RBRACE" || is ps "RPAREN"

let opt_noSeqTerm (ps:pstate) : ML (option term) =
  if at_stmt_end ps || is ps "SEMICOLON" then None else Some (p_noSeqTerm ps)

(* ---------------------------------------------------------------------- *)
(* Separation logic propositions and computation types                    *)
(* ---------------------------------------------------------------------- *)

(* pulseSLProp: typX(tmEqWith(appTermNoRecordExp)) *)
let rec p_slprop (ps:pstate) : ML term =
  let i0 = !ps.idx in
  let k = peek_kind ps in
  if is_quantifier_kind k then begin
    let t = advance ps in
    let bs = binders ps in
    ignore (expect ps "DOT");
    let i_dot = !ps.idx in
    let trigger =
      if accept ps "LBRACE_COLON_PATTERN" then begin
        let pats = sep_nonempty ps "DISJUNCTION" (fun ps -> sep_nonempty ps "SEMICOLON" app_term_full) in
        ignore (expect ps "RBRACE");
        pats
      end else []
    in
    let e = p_slprop ps in
    match bs with
    | [] ->
      E.raise_error_text (rng ps i0 i_dot) Codes.Fatal_MissingQuantifierBinder "Missing binders for a quantifier"
    | _ ->
      let idents = idents_of_binders bs (rng ps i0 i_dot) in
      let q =
        match k with
        | "FORALL" -> QForall (bs, (idents, trigger), e)
        | "EXISTS" -> QExists (bs, (idents, trigger), e)
        | "FORALL_OP" -> QuantOp (mk_id_tok ps t ("forall" ^ t.text), bs, (idents, trigger), e)
        | _ -> QuantOp (mk_id_tok ps t ("exists" ^ t.text), bs, (idents, trigger), e)
      in
      mk_term q (loc ps i0) Formula
  end
  else p_tmEqNoRef ps

(* returns *)
let p_returns (ps:pstate) : ML computation_annot' =
  ignore (expect ps "RETURNS");
  if (is ps "IDENT" || is ps "UNDERSCORE") && peek_kind_n ps 1 = "COLON" then begin
    let i = lidentOrUnderscore ps in
    ignore (expect ps "COLON");
    Returns (Some i, p_tmNoEqNoRef ps)
  end
  else Returns (None, p_tmNoEqNoRef ps)

let is_annot_start (ps:pstate) : ML bool =
  let k = peek_kind ps in
  k = "PRESERVES" || k = "REQUIRES" || k = "ENSURES" || k = "RETURNS" || k = "OPENS"

(* pulseComputationAnnot1 *)
let p_annot (ps:pstate) : ML computation_annot =
  let i0 = !ps.idx in
  let a =
    match peek_kind ps with
    | "PRESERVES" -> ignore (advance ps); Preserves (p_slprop ps)
    | "REQUIRES" -> ignore (advance ps); Requires (p_slprop ps)
    | "ENSURES" -> ignore (advance ps); Ensures (p_slprop ps)
    | "RETURNS" -> p_returns ps
    | "OPENS" -> ignore (advance ps); Opens (p_appTermNoRecordExp ps)
    | _ -> fail ps
  in
  (a, loc ps i0)

(* pulseComputationType *)
let p_comp_type (ps:pstate) : ML computation_type =
  let i0 = !ps.idx in
  let literally = accept ps "NOREWRITE" in
  let rec annots () : ML (list computation_annot) =
    if is_annot_start ps then let a = p_annot ps in a :: annots ()
    else []
  in
  let annots = annots () in
  (* Like Menhir: an empty optional_norewrite starts at the end of the previous token *)
  let r = if literally then loc ps i0 else eps_loc ps i0 in
  mk_comp ST literally annots r

(* ensuresSLProp *)
let p_ensures_slprop (ps:pstate) : ML ensures_slprop =
  let ret =
    if accept ps "RETURNS" then begin
      let i = lidentOrUnderscore ps in
      ignore (expect ps "COLON");
      Some (i, p_term ps)
    end else None
  in
  ignore (expect ps "ENSURES");
  let s = p_slprop ps in
  let opens = if accept ps "OPENS" then Some (p_appTermNoRecordExp ps) else None in
  (ret, s, opens)

let is_ensures_start (ps:pstate) : ML bool = is ps "ENSURES" || is ps "RETURNS"

let opt_ensures_slprop (ps:pstate) : ML (option ensures_slprop) =
  if is_ensures_start ps then Some (p_ensures_slprop ps) else None

(* ---------------------------------------------------------------------- *)
(* The type of a Pulse function, as an F* term                           *)
(* ---------------------------------------------------------------------- *)

(* fn (x:t1) (y:t2) requires pre ensures post
   is (x:t1) -> (y:t2) -> stt ret_type pre (fun ret_name -> post) *)
let build_fn_type_term (bs:list binder) (comp:computation_type) (r:R.range) : ML term =
  let annots = map fst comp.annots in
  let var (s:string) : ML term = mk_term (Var (lid_of_ids [mk_ident (s, r)])) r Un in
  let star (t1 t2:term) : ML term = mk_term (Op (mk_ident ("**", r), [t1; t2])) r Un in
  let star_join (ts:list term) : ML term =
    match ts with
    | [] -> var "emp"
    | t :: rest -> fold_left star t rest
  in
  let reqs = filter_map (function Requires t | Preserves t -> Some t | _ -> None) annots in
  let enss = filter_map (function Ensures t | Preserves t -> Some t | _ -> None) annots in
  let ret_info = tryPick (function Returns (id_opt, ty) -> Some (id_opt, ty) | _ -> None) annots in
  let opens = tryPick (function Opens t -> Some t | _ -> None) annots in
  let ret_ty = match ret_info with Some (_, ty) -> ty | None -> var "unit" in
  let ret_name = match ret_info with Some (Some id, _) -> id | _ -> mk_ident ("_", r) in
  let pre = star_join reqs in
  let post = star_join enss in
  let post_pat = mk_pattern (PatVar (ret_name, None, [])) r in
  let post_lam = mk_term (Abs ([post_pat], post)) r Un in
  let stt_name =
    match comp.tag with
    | ST -> "stt" | STDiv -> "stt_div" | STGhost -> "stt_ghost"
    | STAtomic -> "stt_atomic" | STUnobservable -> "stt_unobservable"
  in
  let stt_var = var stt_name in
  let stt_app =
    match comp.tag with
    | ST | STDiv ->
      mkApp stt_var [(ret_ty, Nothing); (pre, Nothing); (post_lam, Nothing)] r
    | STGhost | STAtomic | STUnobservable ->
      let inames = match opens with Some t -> t | None -> var "emp_inames" in
      mkApp stt_var [(ret_ty, Nothing); (inames, Nothing); (pre, Nothing); (post_lam, Nothing)] r
  in
  mk_term (Product (bs, stt_app)) r Type_level

let r_fn_type (ps:pstate) (_:ctx) : ML term =
  let i0 = !ps.idx in
  let q = qual_opt_fn ps in
  let bs = binders ps in
  let comp = with_computation_tag (p_comp_type ps) q in
  build_fn_type_term bs comp (loc ps i0)

(* In pulseparser.mly, this is a production of both [typ] and
   [simpleArrow]. Here it may start a term at the precedence of arrows
   (so it may also be the codomain of an arrow), and it is a [typ]. *)
let pulse_leading_rules : list (string & leading_rule) = [
  "FN",           lrule "fn_type" 30 10 always r_fn_type;
  "GHOST",        lrule "fn_type" 30 10 (next_is "FN") r_fn_type;
  "ATOMIC",       lrule "fn_type" 30 10 (next_is "FN") r_fn_type;
  "UNOBSERVABLE", lrule "fn_type" 30 10 (next_is "FN") r_fn_type;
  "DIVERGENT",    lrule "fn_type" 30 10 (next_is "FN") r_fn_type;
]

let pulse_grammar : grammar = add_all_leading fstar_grammar pulse_leading_rules

(* ---------------------------------------------------------------------- *)
(* Statements                                                             *)
(* ---------------------------------------------------------------------- *)

let with_binders (ps:pstate) : ML (list binder) =
  ignore (expect ps "WITH");
  let bs = binders ps in
  if Nil? bs then fail ps;
  ignore (expect ps "DOT");
  bs

let optional_names (ps:pstate) : ML (option (list lident)) =
  if accept ps "LBRACK" then begin
    let l = sep_nonempty ps "SEMICOLON" p_qlident in
    ignore (expect ps "RBRACK");
    Some l
  end else None

let opt_by (ps:pstate) : ML (option term) =
  if accept ps "BY" then Some (p_noSeqTerm ps) else None

(* rewriteBody *)
let rewrite_body (ps:pstate) : ML hint_type =
  if accept ps "EACH" then begin
    let pairs = sep_nonempty ps "COMMA" (fun ps ->
      let x = app_term_full ps in
      ignore (expect ps "AS");
      let y = app_term_full ps in
      (x, y))
    in
    let goal = if accept ps "IN" then Some (p_slprop ps) else None in
    let tac = opt_by ps in
    RENAME (pairs, goal, tac)
  end else begin
    let p1 = p_slprop ps in
    ignore (expect ps "AS");
    let p2 = p_slprop ps in
    let tac = opt_by ps in
    REWRITE (p1, p2, tac)
  end

(* A proof hint, after its optional binders *)
let proof_hint (ps:pstate) (bs:list binder) : ML stmt' =
  let ht =
    match (advance ps).kind with
    | "REWRITE" -> rewrite_body ps
    | "ASSERT" -> ASSERT (p_slprop ps)
    | "ASSUME" -> ASSUME (p_slprop ps)
    | "UNFOLD" -> let ns = optional_names ps in UNFOLD (ns, p_slprop ps)
    | "FOLD" -> let ns = optional_names ps in FOLD (ns, p_slprop ps)
    | "UNDERSCORE" -> if Nil? bs then (backup ps 1; fail ps) else WILD
    | _ -> backup ps 1; fail ps
  in
  mk_proof_hint_with_binders ht bs

let rec p_stmt (ps:pstate) : ML stmt =
  if at_stmt_end ps then begin
    let r = rng ps !ps.idx !ps.idx in
    mk_stmt (mk_unit r) r
  end
  else p_stmt_nonempty ps

and p_stmt_nonempty (ps:pstate) : ML stmt =
  let i0 = !ps.idx in
  (* A [let] without [norewrite] or a local [fn] without qualifier starts
     with an empty nonterminal in the Menhir grammar *)
  let k = (tok_at ps i0).L.kind in
  let loc : pstate -> pos -> ML R.range = if k = "LET" || k = "FN" then eps_loc else loc in
  let s1 = p_stmt_noseq ps in
  let s1 = mk_stmt s1 (loc ps i0) in
  if accept ps "SEMICOLON" && not (at_stmt_end ps) then begin
    let s2 = p_stmt_nonempty ps in
    mk_stmt (mk_sequence s1 s2) (loc ps i0)
  end
  else s1

and p_braced_stmt (ps:pstate) : ML stmt =
  ignore (expect ps "LBRACE");
  let s = p_stmt ps in
  ignore (expect ps "RBRACE");
  s

(* pulseLambda *)
and p_lambda (ps:pstate) : ML lambda =
  let i0 = !ps.idx in
  let bs = binders ps in
  let r : pstate -> pos -> ML R.range = if !ps.idx = i0 then eps_loc else loc in
  let body = p_braced_stmt ps in
  mk_lambda bs None body (r ps i0)

(* list(termPulseLambda) *)
and p_lambda_args (ps:pstate) : ML (list lambda) =
  if accept ps "FN" then
    let l = p_lambda ps in
    l :: p_lambda_args ps
  else []

(* ifStmt *)
and p_if (ps:pstate) : ML stmt' =
  ignore (expect ps "IF");
  let i_t = !ps.idx in
  let tm = p_appTermNoRecordExp ps in
  let head = mk_stmt (mk_expr tm []) (loc ps i_t) in
  let req = if accept ps "REQUIRES" then Some (p_slprop ps) else None in
  let vp = opt_ensures_slprop ps in
  let th = p_braced_stmt ps in
  let i_e = !ps.idx in
  let els =
    if accept ps "ELSE" then begin
      if is ps "IF" then
        let s = p_if ps in
        Some (mk_stmt s (loc ps i_e))
      else Some (p_braced_stmt ps)
    end else None
  in
  mk_if head req vp th els

(* fnBody *)
and p_fn_body (ps:pstate) : ML (either (computation_type & option term & stmt) (lambda & option term)) =
  if accept ps "COLON" then begin
    let typ = if is ps "EQUALS" then None else Some (app_term_full ps) in
    ignore (expect ps "EQUALS");
    let lam = p_lambda ps in
    Inr (lam, typ)
  end else begin
    let asc = p_comp_type ps in
    let measure = if accept ps "DECREASES" then Some (p_appTermNoRecordExp ps) else None in
    let body = p_braced_stmt ps in
    Inl (asc, measure, body)
  end

(* letMutInit *)
and p_let_init (ps:pstate) : ML let_init =
  let i0 = !ps.idx in
  if accept ps "EQUALS" then begin
    if is ps "IF" then
      match attempt ps (fun () -> p_if ps) with
      | Some s -> Stmt_initializer (mk_stmt s (loc ps i0))
      | None -> default_init ps
    else if accept ps "LBRACK_BAR" then begin
      let v = p_noSeqTerm ps in
      if accept ps "SEMICOLON" then begin
        let n = p_noSeqTerm ps in
        ignore (expect ps "BAR_RBRACK");
        Array_initializer { init = Some v; len = n }
      end else begin
        ignore (expect ps "BAR_RBRACK");
        Array_initializer { init = None; len = v }
      end
    end
    else default_init ps
  end
  else Default_initializer (None, [])

and default_init (ps:pstate) : ML let_init =
  let s = p_noSeqTerm ps in
  let args = p_lambda_args ps in
  Default_initializer (Some s, args)

(* letPattern *)
and p_let_pattern (ps:pstate) : ML (list term & pattern) =
  let attributed =
    if is ps "LBRACK_AT_AT_AT" then
      attempt ps (fun () ->
        let attrs = binderAttributes ps in
        ignore (expect ps "LPAREN");
        let p = tuplePattern ps in
        ignore (expect ps "RPAREN");
        (attrs, p))
    else None
  in
  match attributed with
  | Some r -> r
  | None -> ([], tuplePattern ps)

(* pulseMatchBranch *)
and p_match_branch (ps:pstate) : ML (bool & pattern & stmt) =
  let norw = accept ps "NOREWRITE" in
  let pat = tuplePattern ps in
  ignore (expect ps "RARROW");
  let e = p_braced_stmt ps in
  (norw, pat, e)

and p_while_invariant (ps:pstate) : ML (list while_invariant1) =
  let inv =
    match peek_kind ps with
    | "INVARIANT" -> ignore (advance ps); Some (LoopInvariant (p_slprop ps))
    | "ENSURES" -> ignore (advance ps); Some (LoopEnsures (p_appTermNoRecordExp ps))
    | "REQUIRES" -> ignore (advance ps); Some (LoopRequires (p_appTermNoRecordExp ps))
    | "DECREASES" -> ignore (advance ps); Some (Decreases (p_appTermNoRecordExp ps))
    | _ -> None
  in
  match inv with
  | Some i -> i :: p_while_invariant ps
  | None -> []

(* pulseStmtNoSeq *)
and p_stmt_noseq (ps:pstate) : ML stmt' =
  let i0 = !ps.idx in
  match peek_kind ps with
  | "OPEN" ->
    ignore (advance ps);
    mk_open (p_quident ps)
  | "NOREWRITE"
  | "LET" ->
    let norw = accept ps "NOREWRITE" in
    ignore (expect ps "LET");
    let q = if accept ps "MUT" then Some MUT else None in
    let attrs, p = p_let_pattern ps in
    let typ = if accept ps "COLON" then Some (app_term_full ps) else None in
    let init = p_let_init ps in
    mk_let_binding norw q attrs p typ init
  | "IF" -> p_if ps
  | "WHILE" ->
    ignore (advance ps);
    ignore (expect ps "LPAREN");
    let tm = p_stmt ps in
    ignore (expect ps "RPAREN");
    let inv = p_while_invariant ps in
    let body = p_braced_stmt ps in
    mk_while tm inv body
  | "INTRO" ->
    ignore (advance ps);
    let p = p_slprop ps in
    ignore (expect ps "WITH");
    let rec ws () : ML (list term) =
      let w, _ = indexing_term ps in
      if is_atomic_start ps then w :: ws () else [w]
    in
    mk_intro p (ws ())
  | "WITH" ->
    let bs = with_binders ps in
    proof_hint ps bs
  | "REWRITE" | "ASSERT" | "ASSUME" | "UNFOLD" | "FOLD" ->
    proof_hint ps []
  | "SHOW_PROOF_STATE" ->
    let t = advance ps in
    mk_proof_hint_with_binders (SHOW_PROOF_STATE (tok_rng ps t)) []
  | "CALC" ->
    mk_expr (r_calc ps dflt) []
  | "LBRACE" ->
    let body = p_braced_stmt ps in
    if is_ensures_start ps || is ps "LABEL" then begin
      let post = opt_ensures_slprop ps in
      ignore (expect ps "LABEL");
      let lbl = p_lident ps in
      ignore (expect ps "COLON");
      mk_forward_jump_label body lbl post
    end
    else mk_block body
  | "LABEL" ->
    ignore (advance ps);
    let lbl = p_lident ps in
    ignore (expect ps "COLON");
    let body = p_braced_stmt ps in
    let post = opt_ensures_slprop ps in
    mk_forward_jump_label body lbl post
  | "MATCH" ->
    ignore (advance ps);
    let i_t = !ps.idx in
    let tm = p_appTermNoRecordExp ps in
    let head = mk_stmt (mk_expr tm []) (loc ps i_t) in
    let c = opt_ensures_slprop ps in
    ignore (expect ps "LBRACE");
    let rec brs () : ML (list (bool & pattern & stmt)) =
      if is ps "RBRACE" then []
      else let b = p_match_branch ps in b :: brs ()
    in
    let brs = brs () in
    ignore (expect ps "RBRACE");
    mk_match head c brs
  | "PRAGMA_SET_OPTIONS" ->
    ignore (advance ps);
    let options = (expect ps "STRING").text in
    let s = p_braced_stmt ps in
    mk_pragma_set_options options s
  | "GOTO" ->
    ignore (advance ps);
    let lbl = p_lident ps in
    mk_goto lbl (opt_noSeqTerm ps)
  | "DEFER" ->
    ignore (advance ps);
    let pre = p_appTermNoRecordExp ps in
    let h = p_braced_stmt ps in
    mk_defer pre h
  | "RETURN" ->
    ignore (advance ps);
    mk_return (opt_noSeqTerm ps)
  | "CONTINUE" -> ignore (advance ps); mk_continue
  | "BREAK" -> ignore (advance ps); mk_break
  | k ->
    if k = "FN" || (is_qual_kind k && peek_kind_n ps 1 = "FN") then begin
      (* localFnDefn *)
      let q = qual_opt_fn ps in
      let lid = lidentOrOperator ps in
      let bs = binders ps in
      let body = p_fn_body ps in
      let r = if k = "FN" then eps_loc ps i0 else loc ps i0 in
      let fndefn = mk_fn_defn' q lid false [] bs body r in
      let pat = mk_pattern (PatVar (lid, None, [])) r in
      mk_let_binding false None [] pat None (Lambda_initializer fndefn)
    end
    else if lookahead ps (fun () -> ignore (indexing_term ps); ignore (expect ps "LARROW")) then begin
      let e1, _ = indexing_term ps in
      ignore (expect ps "LARROW");
      let e3 = p_noSeqTerm ps in
      match e1.tm with
      | Op (op, [arr; ix]) when string_of_id op = ".()" ->
        mk_array_assignment arr ix e3
      | _ ->
        syntax_error (loc ps i0) "Expected an array assignment of the form x.(i) <- v"
    end
    else begin
      let tm = p_tmEq ps in
      let args = p_lambda_args ps in
      mk_expr tm args
    end

(* ---------------------------------------------------------------------- *)
(* Declarations                                                           *)
(* ---------------------------------------------------------------------- *)

let univ_params (ps:pstate) : ML (list ident) =
  let rec go () : ML (list ident) =
    if accept ps "UNIV_HASH" then let n = p_lident ps in n :: go ()
    else []
  in
  go ()

let start_of_next_pulse_decl (k:string) : bool =
  FStar.List.Tot.mem k start_of_next_decl_kinds || is_qual_kind k || k = "FN"

(* pulseDecl *)
let p_pulse_decl (ps:pstate) : ML S.decl =
  let i0 = !ps.idx in
  if accept ps "LET" then begin
    ignore (expect ps "PREDICATE");
    let lid = lidentOrOperator ps in
    let bs = binders ps in
    ignore (expect ps "EQUALS");
    let body = p_term ps in
    SlpropDefn (mk_slprop_defn lid bs body [] (loc ps i0))
  end else begin
    let q = qual_opt_fn ps in
    let is_rec = accept ps "REC" in
    let lid = lidentOrOperator ps in
    let us = univ_params ps in
    let bs = binders ps in
    if accept ps "COLON" then begin
      let typ =
        if is ps "EQUALS" || start_of_next_pulse_decl (peek_kind ps) then None
        else Some (app_term_full ps)
      in
      if accept ps "EQUALS" then begin
        let lam = p_lambda ps in
        FnDefn (mk_fn_defn' q lid is_rec us bs (Inr (lam, typ)) (loc ps i0))
      end else
        syntax_error (loc ps i0) "Ascriptions of lambdas without bodies are not yet supported"
    end else begin
      let asc = p_comp_type ps in
      if is ps "DECREASES" || is ps "LBRACE" then begin
        let measure = if accept ps "DECREASES" then Some (p_appTermNoRecordExp ps) else None in
        let body = p_braced_stmt ps in
        FnDefn (mk_fn_defn' q lid is_rec us bs (Inl (asc, measure, body)) (loc ps i0))
      end else begin
        let asc = with_computation_tag asc q in
        FnDecl (mk_fn_decl lid us bs (Inl asc) [] (loc ps i0))
      end
    end
  end

let is_pulse_decl_start (ps:pstate) : ML bool =
  let k = peek_kind ps in
  k = "FN" || is_qual_kind k || (k = "LET" && peek_kind_n ps 1 = "PREDICATE")

(* incrementalLangDecl, without the token that follows *)
let p_lang_decl (ps:pstate) : ML (list (either S.decl FStarC.Parser.AST.decl)) =
  match p_no_decoration_decl ps with
  | Some ds -> map Inr ds
  | None ->
    let ds = decorations ps in
    if is_pulse_decl_start ps then
      [Inl (S.add_decorations (p_pulse_decl ps) ds)]
    else
      map (fun d -> Inr (FStarC.Parser.AST.add_decorations d ds)) (p_decoratable_decl ps [])

(* ---------------------------------------------------------------------- *)
(* Entry points, used by PulseSyntaxExtension.ASTBuilder                *)
(* ---------------------------------------------------------------------- *)

let start_at (contents:string) (r:R.range) : ML (pstate & list (string & R.range)) =
  let p = R.start_of_range r in
  start_with rewrite_token (R.file_of_range r) contents (R.line_of_pos p) (R.col_of_pos p)

let error_msg (e:E.error) : ML (list Pp.document & R.range) =
  let (_, msg, r, _) = e in
  (msg, r)

let parse_decl (contents:string) (r:R.range)
  : ML (either S.decl (option (list Pp.document & R.range)))
= try
    let ps, _ = start_at contents r in
    Inl (run_with pulse_grammar ps (fun () ->
      let d = p_pulse_decl ps in
      ignore (expect ps "EOF");
      d))
  with
  | E.Error e -> Inr (Some (error_msg e))

let parse_peek_id (contents:string) (r:R.range)
  : ML (either string (list Pp.document & R.range))
= try
    let ps, _ = start_at contents r in
    Inl (run_with pulse_grammar ps (fun () ->
      let _ = qual_opt_fn ps in
      ignore (accept ps "REC");
      string_of_id (lidentOrOperator ps)))
  with
  | E.Error e -> Inr (error_msg e)

(* The comments are left in the buffer of FStarC.Parser.AST.Util, where
   FStarC.Parser.Frontend collects them; on an error, only those before the
   token where parsing stopped. *)
let parse_lang (contents:string) (r:R.range)
  : ML (either (list (either S.decl FStarC.Parser.AST.decl) &
                option (Codes.error_code & E.error_message & R.range))
               (option (list Pp.document & R.range)))
= try
    let ps, comments = start_at contents r in
    let ds, err = parse_incremental_gen pulse_grammar ps p_lang_decl start_of_next_pulse_decl in
    let comments =
      match err with
      | None -> comments
      | Some _ ->
        let f = FStarC.SmallInt.max !ps.furthest !ps.idx in
        drop (length comments - (tok_at ps f).ncom) comments
    in
    FStarC.Parser.AST.Util.add_comments comments;
    Inl (ds, err)
  with
  | E.Error e -> Inr (Some (error_msg e))

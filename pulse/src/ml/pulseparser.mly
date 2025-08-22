%{
(*
Warning: 27 states have shift/reduce conflicts.
Warning: one state has reduce/reduce conflicts.
Warning: 342 shift/reduce conflicts were arbitrarily resolved.
Warning: one reduce/reduce conflict was arbitrarily resolved.
Warning: 234 end-of-stream conflicts were arbitrarily resolved.
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Fstarcompiler
open Prims
open FStar_Pervasives
open FStarC_Errors
open FStarC_List
open FStarC_Util
open FStarC_Range
open FStarC_Options
(* TODO : these files should be deprecated and removed *)
open FStarC_Syntax_Syntax
open FStarC_Parser_Const
open FStarC_Syntax_Util
open FStarC_Parser_AST
open FStarC_Parser_Util
open FStarC_Const
open FStarC_Ident
open FStar_String
module PulseSyntaxExtension_Sugar = PulseSyntaxExtension_Sugar

let mk_meta_tac m = Meta m

let old_attribute_syntax_warning =
  "The `[@ ...]` syntax of attributes is deprecated. \
   Use `[@@ a1; a2; ...; an]`, a semi-colon separated list of attributes, instead"

let do_notation_deprecation_warning = "The lightweight do notation [x <-- y; z] or [x ;; z] is deprecated, use let operators (i.e. [let* x = y in z] or [y ;* z], [*] being any sequence of operator characters) instead."

let none_to_empty_list x =
  match x with
  | None -> []
  | Some l -> l

let as_aqual (q:unit option) =
    match q with
    | None -> None
    | Some _ -> Some Implicit

let pos_of_lexpos (p:Lexing.position) = FStarC_Parser_Util.pos_of_lexpos p

let with_computation_tag (c:PulseSyntaxExtension_Sugar.computation_type) t =
  match t with
  | None -> c
  | Some t -> { c with tag = t }

let mk_fn_defn q id is_rec us bs body range =
    match body with
    | Inl (ascription, measure, body) ->
      let ascription = with_computation_tag ascription q in 
      PulseSyntaxExtension_Sugar.mk_fn_defn id is_rec us (List.flatten bs) (Inl ascription) measure (Inl body) range

    | Inr (lambda, typ) ->
      PulseSyntaxExtension_Sugar.mk_fn_defn id is_rec us (List.flatten bs) (Inr typ) None (Inr lambda) range

let add_decorations decors ds =
  List.map (function
    | Inl p -> Inl (PulseSyntaxExtension_Sugar.add_decorations p decors)
    | Inr d -> Inr (FStarC_Parser_AST.add_decorations d decors)) ds

%}

/* pulse specific tokens; rest are inherited from F* */
%token MUT FN INVARIANT WHILE REF PARALLEL REWRITE FOLD EACH NOREWRITE
%token GHOST ATOMIC UNOBSERVABLE
%token WITH_INVS OPENS  SHOW_PROOF_STATE
%token PRESERVES

%start pulseDeclEOF
%start peekFnId
%start iLangDeclOrEOF
%type <PulseSyntaxExtension_Sugar.decl> pulseDeclEOF
%type <string> peekFnId
%type <(((PulseSyntaxExtension_Sugar.decl, FStarC_Parser_AST.decl) either) list * FStarC_Sedlexing.snap option) option> iLangDeclOrEOF
%%

maybeRec:
  | REC
    { true }
  |
    { false }

/* This is to just peek at the name of the top-level definition */
peekFnId:
  | q=option(qual) FN maybeRec id=lidentOrOperator
      { FStarC_Ident.string_of_id id }

univParam:
  | UNIV_HASH n=lident { n }

univParams:
  | ns=list(univParam) { ns }

qual:
  | GHOST { PulseSyntaxExtension_Sugar.STGhost }
  | ATOMIC { PulseSyntaxExtension_Sugar.STAtomic }
  | UNOBSERVABLE { PulseSyntaxExtension_Sugar.STUnobservable }

startOfNextPulseDeclToken:
 | i=startOfNextDeclToken { i }
 | qual { None }
 | FN { None }

iLangDeclOrEOF:
  | EOF { None }
  | ds=incrementalLangDecl { Some ds }

incrementalLangDecl:
  | ds=list(decoration) d=declBody snap=startOfNextPulseDeclToken { add_decorations ds d,snap }
  | d=noDecorationDecl snap=startOfNextPulseDeclToken { List.map (fun x -> Inr x) d,snap }

declBody:
  | p=pulseDecl { [Inl p] }
  | d=decoratableDecl { List.map (fun x -> Inr x) d }

pulseDecl:
  | q=qualOptFn (* workaround what seems to be a menhir bug *)
    isRec=maybeRec lid=lidentOrOperator us=univParams bs=pulseBinderList
    rest=pulseAscriptionMaybeBody
    {
      let decors = [] in
      match rest with
      | Inl (ascription, None) ->
        let open PulseSyntaxExtension_Sugar in
        let ascription = with_computation_tag ascription q in
        FnDecl (mk_fn_decl lid us (List.flatten bs) (Inl ascription) decors (rr $loc))
      
      | Inl (ascription, Some (measure, body)) ->
        let body = Inl (ascription, measure, body) in
        PulseSyntaxExtension_Sugar.FnDefn (mk_fn_defn q lid isRec us bs body decors (rr $loc))

      | Inr (typ, Some lambda) ->
        let body = Inr (lambda, typ) in
        PulseSyntaxExtension_Sugar.FnDefn (mk_fn_defn q lid isRec us bs body decors (rr $loc))

      | Inr (typ, None) ->
        raise_error_text (rr $loc) Fatal_SyntaxError "Ascriptions of lambdas without bodies are not yet supported"
    }
 
(* defining this as two tokens, option(qual) FN, seems to cause menhir to report an
   incorrect range when the first token is empty *)
qualOptFn:
  | FN { None }
  | q=qual FN { Some q }

pulseAscriptionMaybeBody:
  | ascription=pulseComputationType body=option(pulseBody)
    { Inl (ascription, body) }
  | COLON typ=option(appTerm) lam=option(eqPulseLambda) 
    { Inr(typ, lam) }

eqPulseLambda:
  | EQUALS lambda=pulseLambda
     { lambda }

pulseBody:
  | measure=option(DECREASES m=appTermNoRecordExp {m})
    LBRACE body=pulseStmt RBRACE
    {
      (measure, body)
    }

/* This is the main entry point for the pulse parser */
pulseDeclEOF:
  | p=pulseDecl EOF
    {
      p
    }

pulseBinderList:
  /* |  { [] } We don't yet support nullary functions */
  | bs=nonempty_list(multiBinder)
    {  bs }

localFnDefn:
  | q=option(qual) FN lid=lidentOrOperator
    bs=pulseBinderList
    body=fnBody
    {
      lid, mk_fn_defn q lid false [] bs body [] (rr $loc)
    }

fnBody:
  | ascription=pulseComputationType
    measure=option(DECREASES m=appTermNoRecordExp {m})
    LBRACE body=pulseStmt RBRACE
    {
      Inl (ascription, measure, body)
    }

  | COLON typ=option(appTerm) EQUALS lambda=pulseLambda
    { Inr (lambda, typ) }

ret_ty:
  | r=tmNoEqNoRecordWith(appTermNoRecordExp) {r}

returns:
  | RETURNS i=lidentOrUnderscore COLON r=ret_ty { PulseSyntaxExtension_Sugar.Returns (Some i, r) }
  | RETURNS r=ret_ty { PulseSyntaxExtension_Sugar.Returns (None, r) }

pulseComputationAnnot1_:
  | PRESERVES t=pulseSLProp { PulseSyntaxExtension_Sugar.Preserves t }
  | REQUIRES t=pulseSLProp { PulseSyntaxExtension_Sugar.Requires t }
  | ENSURES t=pulseSLProp { PulseSyntaxExtension_Sugar.Ensures t }
  | r=returns {r}
  | OPENS inv=appTermNoRecordExp { PulseSyntaxExtension_Sugar.Opens inv }

pulseComputationAnnot1:
  | a=pulseComputationAnnot1_ { (a, rr $loc) }

pulseComputationType:
  | annots=list(pulseComputationAnnot1)
    {
        PulseSyntaxExtension_Sugar.mk_comp ST annots (rr $loc)
    }

optional_norewrite:
  | NOREWRITE { true }
  | { false }

while_invariant1:
  | INVARIANT i=lident DOT v=pulseSLProp
    { PulseSyntaxExtension_Sugar.Old (i, v) }
  | INVARIANT v=pulseSLProp
    { PulseSyntaxExtension_Sugar.New v }

while_invariant:
  | is=list(while_invariant1) { is }

pulseStmtNoSeq:
  | OPEN i=quident
    { PulseSyntaxExtension_Sugar.mk_open i }
  | tm=appTerm o=option(LARROW v=noSeqTerm { v })
    {
        match o, tm.tm with
        | None, _ ->
          PulseSyntaxExtension_Sugar.mk_expr tm

        | Some arr_elt, Op(op, [arr;ix]) when FStarC_Ident.string_of_id op = ".()" ->
          PulseSyntaxExtension_Sugar.mk_array_assignment arr ix arr_elt

        | _ ->
          raise_error_text (rr $loc) Fatal_SyntaxError "Expected an array assignment of the form x.(i) <- v"
    }
  | lhs=appTermNoRecordExp COLON_EQUALS a=noSeqTerm
    { PulseSyntaxExtension_Sugar.mk_assignment lhs a }
  | norw=optional_norewrite LET q=option(mutOrRefQualifier) p=pulsePattern typOpt=option(preceded(COLON, appTerm)) EQUALS init=bindableTerm
    { PulseSyntaxExtension_Sugar.mk_let_binding norw q p typOpt (Some init) }
  | s=pulseBindableTerm
    { s }
  | WHILE LPAREN tm=pulseStmt RPAREN inv=while_invariant LBRACE body=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_while tm inv body }
  | INTRO p=pulseSLProp WITH ws=nonempty_list(indexingTerm)
    { PulseSyntaxExtension_Sugar.mk_intro p ws }
  | PARALLEL REQUIRES p1=pulseSLProp AND p2=pulseSLProp
             ENSURES q1=pulseSLProp AND q2=pulseSLProp
             LBRACE b1=pulseStmt RBRACE
             LBRACE b2=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_par p1 p2 q1 q2 b1 b2 }
  | bs=withBindersOpt REWRITE body=rewriteBody
    {
        PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders body bs
    }
  | bs=withBindersOpt ASSERT p=pulseSLProp
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (ASSERT p) bs }
  | bs=withBindersOpt ASSUME p=pulseSLProp
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (ASSUME p) bs }
  | bs=withBindersOpt UNFOLD ns=option(names) p=pulseSLProp
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (UNFOLD (ns,p)) bs }
  | bs=withBindersOpt FOLD ns=option(names) p=pulseSLProp
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (FOLD (ns,p)) bs }
  | bs=withBinders UNDERSCORE
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders WILD bs }
  | SHOW_PROOF_STATE
    { PulseSyntaxExtension_Sugar.mk_proof_hint_with_binders (SHOW_PROOF_STATE (rr $loc)) [] }
  | f=localFnDefn
    {
      let id, fndefn = f in
      let pat = mk_pattern (PatVar (id, None, [])) (rr $loc) in
      PulseSyntaxExtension_Sugar.mk_let_binding false None pat None (Some (Lambda_initializer fndefn))
    }
  | LBRACE s=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_block s }
  | p=matchStmt { p }
  
matchStmt:
  | MATCH tm=appTermNoRecordExp c=option(ensuresSLProp) LBRACE brs=list(pulseMatchBranch) RBRACE
    { PulseSyntaxExtension_Sugar.mk_match tm c brs }

bindableTerm:
  | p=pulseBindableTerm { let p = PulseSyntaxExtension_Sugar.mk_stmt p (rr $loc) in Stmt_initializer p }
  | s=noSeqTerm { Default_initializer s }
  | LBRACK_BAR v=noSeqTerm SEMICOLON n=noSeqTerm BAR_RBRACK { Array_initializer { init=v; len=n } }
 
pulseBindableTerm:
  | WITH_INVS names=nonempty_list(atomicTerm) r=option(ensuresSLProp) LBRACE body=pulseStmt RBRACE
    { PulseSyntaxExtension_Sugar.mk_with_invs names body r }
  | p=ifStmt { p }
 
pulseLambda:
  | bs=pulseBinderList
    ascription=option(pulseComputationType)
    LBRACE body=pulseStmt RBRACE
    {
      PulseSyntaxExtension_Sugar.mk_lambda (List.flatten bs) ascription body (rr ($loc))
    }

rewriteBody:
  | EACH pairs=separated_nonempty_list (COMMA, x=appTerm AS y=appTerm { (x, y)}) goal=option(IN t=pulseSLProp { t })
         tac_opt=option(BY tac=noSeqTerm {tac})
    { RENAME(pairs, goal, tac_opt) }
  | p1=pulseSLProp AS p2=pulseSLProp tac_opt=option(BY tac=noSeqTerm {tac})
    { PulseSyntaxExtension_Sugar.REWRITE(p1, p2, tac_opt) }

names:
  | LBRACK l=separated_nonempty_list(SEMICOLON, qlident) RBRACK
    { l }

withBinders:
  | WITH bs=nonempty_list(multiBinder) DOT
    { List.flatten bs }

withBindersOpt:
  | w=withBinders
    { w }
  | { [] }

ensuresSLProp:
  | ret=option(RETURNS i=lidentOrUnderscore COLON r=term { (i, r) }) ENSURES s=pulseSLProp maybe_opens=option(OPENS inv=appTermNoRecordExp { inv })
    { ret, s, maybe_opens }

pulseMatchBranch:
  | norw=optional_norewrite pat=pulsePattern RARROW LBRACE e=pulseStmt RBRACE
    { (norw, pat, e) }

pulsePattern:
  | p=tuplePattern { p }

pulseStmt:
  | s=pulseStmtNoSeq
    { PulseSyntaxExtension_Sugar.mk_stmt s (rr $loc) }
  | s1=pulseStmtNoSeq SEMICOLON s2=option(pulseStmt)
    {
      let s1 = PulseSyntaxExtension_Sugar.mk_stmt s1 (rr ($loc(s1))) in
      match s2 with
      | None -> s1
      | Some s2 -> PulseSyntaxExtension_Sugar.mk_stmt (PulseSyntaxExtension_Sugar.mk_sequence s1 s2) (rr ($loc))
    }

ifStmt:
  | IF tm=appTermNoRecordExp vp=option(ensuresSLProp) LBRACE th=pulseStmt RBRACE e=option(elseBlock)
    { PulseSyntaxExtension_Sugar.mk_if tm vp th e }

elseBlock:
  | ELSE LBRACE p=pulseStmt RBRACE
    { p }
  | ELSE s=ifStmt
    { PulseSyntaxExtension_Sugar.mk_stmt s (rr $loc) }

mutOrRefQualifier:
  | MUT { MUT }
  | REF { REF }

typX(X):
  | t=X { t }

  | q=quantifier bs=binders DOT trigger=trigger e=typX(X)
      {
        match bs with
        | [] ->
          raise_error_text (rr2 $loc(q) $loc($3)) Fatal_MissingQuantifierBinder "Missing binders for a quantifier"
        | _ ->
          let idents = idents_of_binders bs (rr2 $loc(q) $loc($3)) in
          mk_term (q (bs, (idents, trigger), e)) (rr2 $loc(q) $loc(e)) Formula
      }

pulseSLProp:
  | p=typX(tmEqWith(appTermNoRecordExp))
    { p }

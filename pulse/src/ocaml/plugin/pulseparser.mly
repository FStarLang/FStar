%{
(*
 We are expected to have only 6 shift-reduce conflicts in ML and 8 in F#.
 A lot (176) of end-of-stream conflicts are also reported and
 should be investigated...
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Prims
open FStar_Pervasives
open FStar_Errors
open FStar_Compiler_List
open FStar_Compiler_Util
open FStar_Compiler_Range
open FStar_Options
(* TODO : these files should be deprecated and removed *)
open FStar_Syntax_Syntax
open FStar_Parser_Const
open FStar_Syntax_Util
open FStar_Parser_AST
open FStar_Parser_Util
open FStar_Const
open FStar_Ident
open FStar_String
open PulseSugar
module AU = FStar_Parser_AST_Util

let lhs _ = FStar_Compiler_Range.dummyRange
let rhs _ i = FStar_Compiler_Range.dummyRange
let rhs2 _ i j = FStar_Compiler_Range.dummyRange

let mk_meta_tac m = Meta m

let old_attribute_syntax_warning =
  "The `[@ ...]` syntax of attributes is deprecated. \
   Use `[@@ a1; a2; ...; an]`, a semi-colon separated list of attributes, instead"

let do_notation_deprecation_warning =
  "The lightweight do notation [x <-- y; z] or [x ;; z] is deprecated, use let operators (i.e. [let* x = y in z] or [y ;* z], [*] being any sequence of operator characters) instead."

let none_to_empty_list x =
  match x with
  | None -> []
  | Some l -> l

let as_aqual (q:unit option) =
    match q with
    | None -> None
    | Some _ -> Some Implicit
    
let pos_of_lexpos (p:Lexing.position) = FStar_Parser_Util.pos_of_lexpos p

let default_return =
    gen dummyRange,
    mk_term (Var (lid_of_ids [(mk_ident("unit", dummyRange))])) dummyRange Un
    
let rng p1 p2 = FStar_Parser_Util.mksyn_range p1 p2
let r p = rng (fst p) (snd p)
%}

/* pulse specific tokens; rest are inherited from F* */
%token MUT VAR FN INVARIANT WHILE REF PARALLEL REWRITE
%token <string> STRING
%token <string> IDENT
%token <string> NAME
%token <string> TVAR
%token <string> TILDE

/* bool indicates if INT8 was 'bad' max_int+1, e.g. '128'  */
%token <string * bool> INT8
%token <string * bool> INT16
%token <string * bool> INT32
%token <string * bool> INT64
%token <string * bool> INT
%token <string> RANGE

%token <string> UINT8
%token <string> UINT16
%token <string> UINT32
%token <string> UINT64
%token <string> SIZET
%token <string> REAL
%token <FStar_Char.char> CHAR
%token <bool> LET
%token <string> LET_OP
%token <string> AND_OP
%token <string> MATCH_OP
%token <string> IF_OP
/* [SEMICOLON_OP] encodes either:
- [;;], which used to be SEMICOLON_SEMICOLON, or
- [;<OP>], with <OP> a sequence of [op_char] (see FStar_Parser_LexFStar).
*/
%token <string option> SEMICOLON_OP

%token FORALL EXISTS ASSUME NEW LOGIC ATTRIBUTES
%token IRREDUCIBLE UNFOLDABLE INLINE OPAQUE UNFOLD INLINE_FOR_EXTRACTION
%token NOEXTRACT
%token NOEQUALITY UNOPTEQUALITY PRAGMA_SET_OPTIONS PRAGMA_RESET_OPTIONS PRAGMA_PUSH_OPTIONS PRAGMA_POP_OPTIONS PRAGMA_RESTART_SOLVER PRAGMA_PRINT_EFFECTS_GRAPH
%token TYP_APP_LESS TYP_APP_GREATER SUBTYPE EQUALTYPE SUBKIND BY
%token AND ASSERT SYNTH BEGIN ELSE END
%token EXCEPTION FALSE FUN FUNCTION IF IN MODULE DEFAULT
%token MATCH OF
%token FRIEND OPEN REC THEN TRUE TRY TYPE CALC CLASS INSTANCE EFFECT VAL
%token INTRO ELIM
%token INCLUDE
%token WHEN AS RETURNS RETURNS_EQ WITH HASH AMP LPAREN RPAREN LPAREN_RPAREN COMMA LONG_LEFT_ARROW LARROW RARROW
%token IFF IMPLIES CONJUNCTION DISJUNCTION
%token DOT COLON COLON_COLON SEMICOLON
%token QMARK_DOT
%token QMARK
%token EQUALS PERCENT_LBRACK LBRACK_AT LBRACK_AT_AT LBRACK_AT_AT_AT DOT_LBRACK
%token DOT_LENS_PAREN_LEFT DOT_LPAREN DOT_LBRACK_BAR LBRACK LBRACK_BAR LBRACE_BAR LBRACE BANG_LBRACE
%token BAR_RBRACK BAR_RBRACE UNDERSCORE LENS_PAREN_LEFT LENS_PAREN_RIGHT
%token BAR RBRACK RBRACE DOLLAR
%token PRIVATE REIFIABLE REFLECTABLE REIFY RANGE_OF SET_RANGE_OF LBRACE_COLON_PATTERN PIPE_RIGHT
%token NEW_EFFECT SUB_EFFECT LAYERED_EFFECT POLYMONADIC_BIND POLYMONADIC_SUBCOMP SPLICE SPLICET SQUIGGLY_RARROW TOTAL
%token REQUIRES ENSURES DECREASES LBRACE_COLON_WELL_FOUNDED
%token MINUS COLON_EQUALS QUOTE BACKTICK_AT BACKTICK_HASH
%token BACKTICK UNIV_HASH
%token BACKTICK_PERC

%token<string>  OPPREFIX OPINFIX0a OPINFIX0b OPINFIX0c OPINFIX0d OPINFIX1 OPINFIX2 OPINFIX3 OPINFIX4
%token<string>  OP_MIXFIX_ASSIGNMENT OP_MIXFIX_ACCESS
%token<string * string * Lexing.position>  BLOB

/* These are artificial */
%token EOF

%nonassoc THEN
%nonassoc ELSE


%right COLON_COLON
%right AMP

%nonassoc COLON_EQUALS
%left     OPINFIX0a
%left     OPINFIX0b
%left     OPINFIX0c EQUALS
%left     OPINFIX0d
%left     PIPE_RIGHT
%right    OPINFIX1
%left     OPINFIX2 MINUS QUOTE
%left     OPINFIX3
%left     BACKTICK
%right    OPINFIX4

%start pulseDecl
%start peekFnId
%type <PulseSugar.decl> pulseDecl
%type <string> peekFnId
%%

/* This is to just peek at the name of the top-level definition */
peekFnId:
  | FN id=lident
      { FStar_Ident.string_of_id id }

/* This is the main entry point for the pulse parser */
pulseDecl:
  | FN lid=lident bs=nonempty_list(pulseMultiBinder) ascription=pulseComputationType LBRACE body=pulseStmt RBRACE
    {
      let r = rng ($startpos($1)) ($endpos($7)) in
      mk_decl lid (List.flatten bs) ascription body r
    }
    
pulseMultiBinder:
  | LPAREN qual_ids=nonempty_list(q=option(HASH) id=lidentOrUnderscore { (q, id) }) COLON t=appTerm RPAREN
    { List.map (fun (q, id) -> (as_aqual q, id, t)) qual_ids }
  | q=option(HASH) id=lidentOrUnderscore
    { [(as_aqual q, id, mk_term Wild (r ($loc(id))) Un)] }

pulseComputationType:
  | REQUIRES t=pulseVprop
    ret=option(RETURNS i=lidentOrUnderscore COLON r=term { (i, r) })
    ENSURES t2=pulseVprop
    {
        let i, r =
          match ret with
          | Some (i, r) -> i, r
          | None -> default_return
        in
        mk_comp ST t i r t2 (rng ($startpos($1)) ($endpos(t2)))
    }


pulseStmtNoSeq:
  | OPEN i=quident
    { mk_open i }
  | tm=appTerm
    { mk_expr tm }
  | i=lident COLON_EQUALS a=noSeqTerm
    { mk_assignment i a }
  | LET q=option(mutOrRefQualifier) i=lident typOpt=option(appTerm) EQUALS tm=noSeqTerm
    { mk_let_binding q i typOpt (Some tm) }
  | LBRACE s=pulseStmt RBRACE
    { mk_block s }
  | IF tm=appTermNoRecordExp vp=option(returnsVprop) LBRACE th=pulseStmt RBRACE e=option(elseBlock)
    { mk_if tm vp th e }
  | MATCH tm=appTermNoRecordExp c=option(returnsAnnot) LBRACE brs=list(pulseMatchBranch) RBRACE
    { mk_match tm c brs }
  | WHILE LPAREN tm=pulseStmt RPAREN INVARIANT i=lident DOT v=pulseVprop LBRACE body=pulseStmt RBRACE
    { mk_while tm i v body }
  | INTRO p=pulseVprop WITH ws=nonempty_list(indexingTerm)
    { mk_intro p ws }
  | PARALLEL REQUIRES p1=pulseVprop AND p2=pulseVprop
             ENSURES q1=pulseVprop AND q2=pulseVprop
             LBRACE b1=pulseStmt RBRACE
             LBRACE b2=pulseStmt RBRACE
    { mk_par p1 p2 q1 q2 b1 b2 }
  | REWRITE p1=pulseVprop AS p2=pulseVprop
    { mk_rewrite p1 p2 }

%inline
returnsAnnot:
  | RETURNS s=pulseComputationType
    { s }

returnsVprop:
  | RETURNS s=pulseVprop
    { s }

pulseMatchBranch:
  | LBRACE pat=pulsePattern RARROW e=pulseStmt RBRACE
    { (pat, e) }

pulsePattern:
  | p=tuplePattern { p }
  
pulseStmt:
  | s=pulseStmtNoSeq 
    { mk_stmt s (rng ($startpos(s)) ($endpos(s))) }
  | s1=pulseStmtNoSeq SEMICOLON s2=option(pulseStmt)
    {
      let s1 = mk_stmt s1 (rng ($startpos(s1)) ($endpos(s1))) in
      match s2 with
      | None -> s1
      | Some s2 -> mk_stmt (mk_sequence s1 s2) (rng ($startpos(s1)) ($endpos(s2)))
    }

elseBlock:
  | ELSE LBRACE p=pulseStmt RBRACE
    { p }

mutOrRefQualifier:
  | MUT { MUT }
  | REF { REF }

pulseVprop:
  | t=appTermNoRecordExp
    { VPropTerm t }
  | EXISTS bs=nonempty_list(pulseMultiBinder) DOT body=pulseVprop
    { mk_vprop_exists (List.flatten bs) body }

/****************************************************************/
/** F* term syntax **/
/****************************************************************/

attr_letbinding:
  | attr=ioption(attribute) AND lb=letbinding
    { attr, lb }

letoperatorbinding:
  | pat=tuplePattern ascr_opt=ascribeTyp? tm=option(EQUALS tm=term {tm})
    {
        let h tm
	  = ( ( match ascr_opt with
              | None   -> pat
              | Some t -> mk_pattern (PatAscribed(pat, t)) (rng $startpos(pat) $endpos(ascr_opt)) )
	    , tm)
	in
	match pat.pat, tm with
        | _               , Some tm -> h tm
        | PatVar (v, _, _), None    ->
          let v = lid_of_ns_and_id [] v in
          h (mk_term (Var v) (rng $startpos(pat) $endpos(pat)) Expr)
        | _ -> raise_error (Fatal_SyntaxError, "Syntax error: let-punning expects a name, not a pattern")
                           (rng $startpos(ascr_opt) $endpos(ascr_opt))
    }


letbinding:
  |  lid=lidentOrOperator lbp=nonempty_list(patternOrMultibinder) ascr_opt=ascribeTyp? EQUALS tm=term
      {
        let pat = mk_pattern (PatVar(lid, None, [])) (rhs parseState 2) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rhs2 parseState 1 3) in
        let pos = rhs2 parseState 1 6 in
        match ascr_opt with
        | None -> false, (pat, tm)
        | Some t -> false, (mk_pattern (PatAscribed(pat, t)) pos, tm)
      }
  | pat=tuplePattern ascr=ascribeTyp EQUALS tm=term
      { false, (mk_pattern (PatAscribed(pat, ascr)) (rhs2 parseState 1 4), tm) }
  | pat=tuplePattern EQUALS tm=term
      { false, (pat, tm) }

letqualifier:
  | REC         { Rec }
  |             { NoLetQualifier }

(*
 * AR: this should be generalized to:
 *     (a) allow attributes on non-implicit binders
 *     note that in the [@@ case, we choose the Implicit aqual
 *)
aqual:
  | HASH LBRACK t=thunk(tmNoEq) RBRACK { mk_meta_tac t }
  | HASH      { Implicit }
  | DOLLAR    { Equality }

binderAttributes:
  | LBRACK_AT_AT_AT t=semiColonTermList RBRACK { t }

/******************************************************************************/
/*                         Patterns, binders                                  */
/******************************************************************************/

(* disjunction should be allowed in nested patterns *)
disjunctivePattern:
  | pats=separated_nonempty_list(BAR, tuplePattern) { pats }

tuplePattern:
  | pats=separated_nonempty_list(COMMA, constructorPattern)
      { match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) (rhs parseState 1) }

constructorPattern:
  | pat=constructorPattern COLON_COLON pats=constructorPattern
      { mk_pattern (consPat (rhs parseState 3) pat pats) (rhs2 parseState 1 3) }
  | uid=quident args=nonempty_list(atomicPattern)
      {
        let head_pat = mk_pattern (PatName uid) (rhs parseState 1) in
        mk_pattern (PatApp (head_pat, args)) (rhs2 parseState 1 2)
      }
  | pat=atomicPattern
      { pat }

atomicPattern:
  | LPAREN pat=tuplePattern COLON t=simpleArrow phi_opt=refineOpt RPAREN
      {
        let pos_t = rhs2 parseState 2 4 in
        let pos = rhs2 parseState 1 6 in
        mkRefinedPattern pat t true phi_opt pos_t pos
      }
  | LBRACK pats=separated_list(SEMICOLON, tuplePattern) RBRACK
      { mk_pattern (PatList pats) (rhs2 parseState 1 3) }
  | LBRACE record_pat=right_flexible_nonempty_list(SEMICOLON, fieldPattern) RBRACE
      { mk_pattern (PatRecord record_pat) (rhs2 parseState 1 3) }
  | LENS_PAREN_LEFT pat0=constructorPattern COMMA pats=separated_nonempty_list(COMMA, constructorPattern) LENS_PAREN_RIGHT
      { mk_pattern (PatTuple(pat0::pats, true)) (rhs2 parseState 1 5) }
  | LPAREN pat=tuplePattern RPAREN   { pat }
  | tv=tvar                   { mk_pattern (PatTvar (tv, None, [])) (rhs parseState 1) }
  | LPAREN op=operator RPAREN
      { mk_pattern (PatOp op) (rhs2 parseState 1 3) }
  | UNDERSCORE
      { mk_pattern (PatWild (None, [])) (rhs parseState 1) }
  | HASH UNDERSCORE
      { mk_pattern (PatWild (Some Implicit, [])) (rhs parseState 1) }
  | c=constant
      { mk_pattern (PatConst c) (rhs parseState 1) }
  | BACKTICK_PERC q=atomicTerm
      { mk_pattern (PatVQuote q) (rhs2 parseState 1 2) }
  | qual_id=aqualifiedWithAttrs(lident)
    {
      let (aqual, attrs), lid = qual_id in
      mk_pattern (PatVar (lid, aqual, attrs)) (rhs parseState 1) }
  | uid=quident
      { mk_pattern (PatName uid) (rhs parseState 1) }

fieldPattern:
  | p = separated_pair(qlident, EQUALS, tuplePattern)
      { p }
  | lid=qlident
      { lid, mk_pattern (PatVar (ident_of_lid lid, None, [])) (rhs parseState 1) }

  (* (x : t) is already covered by atomicPattern *)
  (* we do *NOT* allow _ in multibinder () since it creates reduce/reduce conflicts when*)
  (* preprocessing to ocamlyacc/fsyacc (which is expected since the macro are expanded) *)
patternOrMultibinder:
  | LBRACE_BAR id=lidentOrUnderscore COLON t=simpleArrow BAR_RBRACE
      { let r = rhs2 parseState 1 5 in
        let w = mk_pattern (PatVar (id, Some TypeClassArg, [])) r in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) r]
      }

  | LBRACE_BAR t=simpleArrow BAR_RBRACE
      { let r = rhs2 parseState 1 3 in
        let id = gen r in
        let w = mk_pattern (PatVar (id, Some TypeClassArg, [])) r in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) r]
      }
  | pat=atomicPattern { [pat] }
  | LPAREN qual_id0=aqualifiedWithAttrs(lident) qual_ids=nonempty_list(aqualifiedWithAttrs(lident)) COLON t=simpleArrow r=refineOpt RPAREN
      {
        let pos = rhs2 parseState 1 7 in
        let t_pos = rhs parseState 5 in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun ((aq, attrs), x) -> mkRefinedPattern (mk_pattern (PatVar (x, aq, attrs)) pos) t false r t_pos pos) qual_ids
      }

binder:
  | aqualifiedWithAttrs_lid=aqualifiedWithAttrs(lidentOrUnderscore)
     {
       let (q, attrs), lid = aqualifiedWithAttrs_lid in
       mk_binder_with_attrs (Variable lid) (rhs parseState 1) Type_level q attrs
     }

  | tv=tvar  { mk_binder (TVariable tv) (rhs parseState 1) Kind None  }
       (* small regression here : fun (=x : t) ... is not accepted anymore *)

multiBinder:
  | LBRACE_BAR id=lidentOrUnderscore COLON t=simpleArrow BAR_RBRACE
      { let r = rhs2 parseState 1 5 in
        [mk_binder (Annotated (id, t)) r Type_level (Some TypeClassArg)]
      }

  | LBRACE_BAR t=simpleArrow BAR_RBRACE
      { let r = rhs2 parseState 1 3 in
        let id = gen r in
        [mk_binder (Annotated (id, t)) r Type_level (Some TypeClassArg)]
      }

  | LPAREN qual_ids=nonempty_list(aqualifiedWithAttrs(lidentOrUnderscore)) COLON t=simpleArrow r=refineOpt RPAREN
     {
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun ((q, attrs), x) ->
         mkRefinedBinder x t should_bind_var r (rhs2 parseState 1 6) q attrs) qual_ids
     }

binders: bss=list(b=binder {[b]} | bs=multiBinder {bs}) { flatten bss }

aqualifiedWithAttrs(X):
  | aq=aqual attrs=binderAttributes x=X { (Some aq, attrs), x }
  | aq=aqual x=X { (Some aq, []), x }
  | attrs=binderAttributes x=X { (None, attrs), x }
  | x=X { (None, []), x }

/******************************************************************************/
/*                      Identifiers, module paths                             */
/******************************************************************************/

qlident:
  | ids=path(lident) { lid_of_ids ids }

quident:
  | ids=path(uident) { lid_of_ids ids }

path(Id):
  | id=Id { [id] }
  | uid=uident DOT p=path(Id) { uid::p }

ident:
  | x=lident { x }
  | x=uident  { x }

qlidentOrOperator:
  | qid=qlident { qid }
  | LPAREN id=operator RPAREN
    { lid_of_ns_and_id [] (id_of_text (compile_op' (string_of_id id) (range_of_id id))) }

%inline lidentOrOperator:
  | id=lident { id }
  | LPAREN id=operator RPAREN
    { mk_ident (compile_op' (string_of_id id) (range_of_id id), range_of_id id) }

matchMaybeOp:
  | MATCH {None}
  | op=MATCH_OP { Some (mk_ident ("let" ^ op, rhs parseState 1)) }

ifMaybeOp:
  | IF {None}
  | op=IF_OP { Some (mk_ident ("let" ^ op, rhs parseState 1)) }

lidentOrUnderscore:
  | id=IDENT { mk_ident(id, rhs parseState 1)}
  | UNDERSCORE { gen (rhs parseState 1) }

lident:
  | id=IDENT { mk_ident(id, rhs parseState 1)}

uident:
  | id=NAME { mk_ident(id, rhs parseState 1) }

tvar:
  | tv=TVAR { mk_ident(tv, rhs parseState 1) }


/******************************************************************************/
/*                            Types and terms                                 */
/******************************************************************************/

thunk(X): | t=X { mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr }

thunk2(X):
  | t=X
     { let u = mk_term (Const Const_unit) (rhs parseState 3) Expr in
       let t = mk_term (Seq (u, t)) (rhs parseState 3) Expr in
       mk_term (Abs ([mk_pattern (PatWild (None, [])) (rhs parseState 3)], t)) (rhs parseState 3) Expr }

ascribeTyp:
  | COLON t=tmArrow(tmNoEq) tacopt=option(BY tactic=thunk(atomicTerm) {tactic}) { t, tacopt }


term:
  | e=noSeqTerm
      { e }
  | e1=noSeqTerm SEMICOLON e2=term
      { mk_term (Seq(e1, e2)) (rhs2 parseState 1 3) Expr }
(* Added this form for sequencing; *)
(* but it results in an additional shift/reduce conflict *)
(* ... which is actually be benign, since the same conflict already *)
(*     exists for the previous production *)
  | e1=noSeqTerm op=SEMICOLON_OP e2=term
      { let t = match op with
        | Some op ->
          let op = mk_ident ("let" ^ op, rhs parseState 2) in
          let pat = mk_pattern (PatWild(None, [])) (rhs parseState 2) in
          LetOperator ([(op, pat, e1)], e2)
        | None   ->
                log_issue (lhs parseState) (Warning_DeprecatedLightDoNotation, do_notation_deprecation_warning);
          Bind(gen (rhs parseState 2), e1, e2)
            in mk_term t (rhs2 parseState 1 3) Expr
      }

match_returning:
  | as_opt=option(AS i=lident {i}) RETURNS t=tmIff {as_opt,t,false}
  | as_opt=option(AS i=lident {i}) RETURNS_EQ t=tmIff {as_opt,t,true}

noSeqTerm:
  | t=typ  { t }
  | e=tmIff SUBTYPE t=tmIff tactic_opt=option(BY tactic=thunk(typ) {tactic})
      { mk_term (Ascribed(e,{t with level=Expr},tactic_opt,false)) (rhs2 parseState 1 4) Expr }
  | e=tmIff EQUALTYPE t=tmIff tactic_opt=option(BY tactic=thunk(typ) {tactic})
      {
        log_issue (lhs parseState)
	          (Warning_BleedingEdge_Feature,
		   "Equality type ascriptions is an experimental feature subject to redesign in the future");
        mk_term (Ascribed(e,{t with level=Expr},tactic_opt,true)) (rhs2 parseState 1 4) Expr
      }
  | e1=atomicTermNotQUident op_expr=dotOperator LARROW e3=noSeqTerm
      {
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      }
  | REQUIRES t=typ
      { mk_term (Requires(t, None)) (rhs2 parseState 1 2) Type_level }
  | ENSURES t=typ
      { mk_term (Ensures(t, None)) (rhs2 parseState 1 2) Type_level }
  | DECREASES t=typ
      { mk_term (Decreases (t, None)) (rhs2 parseState 1 2) Type_level }
  | DECREASES LBRACE_COLON_WELL_FOUNDED t=noSeqTerm RBRACE
      (*
       * decreases clause with relation is written as e1 e2,
       *   where e1 is a relation and e2 is a term
       *
       * this is parsed as an app node, so we destruct the app node
       *)
      { match t.tm with
        | App (t1, t2, _) ->
	  let ot = mk_term (WFOrder (t1, t2)) (rhs2 parseState 3 3) Type_level in
	  mk_term (Decreases (ot, None)) (rhs2 parseState 1 4) Type_level
	| _ ->
	  raise_error (Fatal_SyntaxError,
	    "Syntax error: To use well-founded relations, write e1 e2") (rhs parseState 3) }

  | ATTRIBUTES es=nonempty_list(atomicTerm)
      { mk_term (Attributes es) (rhs2 parseState 1 2) Type_level }
  | op=ifMaybeOp e1=noSeqTerm ret_opt=option(match_returning) THEN e2=noSeqTerm ELSE e3=noSeqTerm
      { mk_term (If(e1, op, ret_opt, e2, e3)) (rhs2 parseState 1 7) Expr }
  | op=ifMaybeOp e1=noSeqTerm ret_opt=option(match_returning) THEN e2=noSeqTerm
      {
        let e3 = mk_term (Const Const_unit) (rhs2 parseState 1 5) Expr in
        mk_term (If(e1, op, ret_opt, e2, e3)) (rhs2 parseState 1 5) Expr
      }
  | TRY e1=term WITH pbs=left_flexible_nonempty_list(BAR, patternBranch)
      {
         let branches = focusBranches (pbs) (rhs2 parseState 1 4) in
         mk_term (TryWith(e1, branches)) (rhs2 parseState 1 4) Expr
      }
  | op=matchMaybeOp e=term ret_opt=option(match_returning) WITH pbs=left_flexible_list(BAR, pb=patternBranch {pb})
      {
        let branches = focusBranches pbs (rhs2 parseState 1 5) in
        mk_term (Match(e, op, ret_opt, branches)) (rhs2 parseState 1 5) Expr
      }
  | LET OPEN t=term IN e=term
      {
            match t.tm with
            | Ascribed(r, rty, None, _) ->
              mk_term (LetOpenRecord(r, rty, e)) (rhs2 parseState 1 5) Expr

            | Name uid ->
              mk_term (LetOpen(uid, e)) (rhs2 parseState 1 5) Expr

            | _ ->
              raise_error (Fatal_SyntaxError, "Syntax error: local opens expects either opening\n\
                                               a module or namespace using `let open T in e`\n\
                                               or, a record type with `let open e <: t in e'`")
                          (rhs parseState 3)
      }

  | attrs=ioption(attribute)
    LET q=letqualifier lb=letbinding lbs=list(attr_letbinding) IN e=term
      {
        let lbs = (attrs, lb)::lbs in
        let lbs = focusAttrLetBindings lbs (rhs2 parseState 2 3) in
        mk_term (Let(q, lbs, e)) (rhs2 parseState 1 6) Expr
      }
  | op=let_op b=letoperatorbinding lbs=list(op=and_op b=letoperatorbinding {(op, b)}) IN e=term
    { let lbs = (op, b)::lbs in
      mk_term (LetOperator ( List.map (fun (op, (pat, tm)) -> (op, pat, tm)) lbs
			   , e)) (rhs2 parseState 1 5) Expr
    }

  | FUNCTION pbs=left_flexible_nonempty_list(BAR, patternBranch)
      {
        let branches = focusBranches pbs (rhs2 parseState 1 2) in
        mk_function branches (lhs parseState) (rhs2 parseState 1 2)
      }

  | ASSUME e=atomicTerm
      { let a = set_lid_range assume_lid (rhs parseState 1) in
        mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2)
      }

  | ASSERT e=atomicTerm tactic_opt=option(BY tactic=thunk2(typ) {tactic})
      {
        match tactic_opt with
        | None ->
          let a = set_lid_range assert_lid (rhs parseState 1) in
          mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2)
        | Some tac ->
          let a = set_lid_range assert_by_tactic_lid (rhs parseState 1) in
          mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e; tac] (rhs2 parseState 1 4)
      }

   | UNDERSCORE BY tactic=thunk(atomicTerm)
     {
         let a = set_lid_range synth_lid (rhs parseState 1) in
         mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [tactic] (rhs2 parseState 1 2)
     }

   | SYNTH tactic=atomicTerm
     {
         let a = set_lid_range synth_lid (rhs parseState 1) in
         mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [tactic] (rhs2 parseState 1 2)
     }

   | CALC rel=atomicTerm LBRACE init=noSeqTerm SEMICOLON steps=list(calcStep) RBRACE
     {
         mk_term (CalcProof (rel, init, steps)) (rhs2 parseState 1 7) Expr
     }

   | INTRO FORALL bs=binders DOT p=noSeqTerm WITH e=noSeqTerm
     {
        mk_term (IntroForall(bs, p, e)) (rhs2 parseState 1 7) Expr
     }

   | INTRO EXISTS bs=binders DOT p=noSeqTerm WITH vs=list(atomicTerm) AND e=noSeqTerm
     {
        if List.length bs <> List.length vs
        then raise_error (Fatal_SyntaxError, "Syntax error: expected instantiations for all binders") (rhs parseState 7)
        else mk_term (IntroExists(bs, p, vs, e)) (rhs2 parseState 1 9) Expr
     }

   | INTRO p=tmFormula IMPLIES q=tmFormula WITH y=singleBinder DOT e=noSeqTerm
     {
        mk_term (IntroImplies(p, q, y, e)) (rhs2 parseState 1 8) Expr
     }

   | INTRO p=tmFormula DISJUNCTION q=tmConjunction WITH lr=NAME e=noSeqTerm
     {
        let b =
            if lr = "Left" then true
            else if lr = "Right" then false
            else raise_error (Fatal_SyntaxError, "Syntax error: _intro_ \\/ expects either 'Left' or 'Right'") (rhs parseState 6)
        in
        mk_term (IntroOr(b, p, q, e))  (rhs2 parseState 1 7) Expr
     }

   | INTRO p=tmConjunction CONJUNCTION q=tmTuple WITH e1=noSeqTerm AND e2=noSeqTerm
     {
        mk_term (IntroAnd(p, q, e1, e2))  (rhs2 parseState 1 8) Expr
     }

   | ELIM FORALL xs=binders DOT p=noSeqTerm WITH vs=list(atomicTerm)
     {
        mk_term (ElimForall(xs, p, vs)) (rhs2 parseState 1 7) Expr
     }

   | ELIM EXISTS bs=binders DOT p=noSeqTerm RETURNS q=noSeqTerm WITH y=singleBinder DOT e=noSeqTerm
     {
        mk_term (ElimExists(bs, p, q, y, e)) (rhs2 parseState 1 11) Expr
     }

   | ELIM p=tmFormula IMPLIES q=tmFormula WITH e=noSeqTerm
     {
        mk_term (ElimImplies(p, q, e)) (rhs2 parseState 1 6) Expr
     }

   | ELIM p=tmFormula DISJUNCTION q=tmConjunction RETURNS r=noSeqTerm WITH x=singleBinder DOT e1=noSeqTerm AND y=singleBinder DOT e2=noSeqTerm
     {
        mk_term (ElimOr(p, q, r, x, e1, y, e2)) (rhs2 parseState 1 14) Expr
     }

   | ELIM p=tmConjunction CONJUNCTION q=tmTuple RETURNS r=noSeqTerm WITH xs=binders DOT e=noSeqTerm
     {
        match xs with
        | [x;y] -> mk_term (ElimAnd(p, q, r, x, y, e)) (rhs2 parseState 1 10) Expr
     }

singleBinder:
  | bs=binders
    {
       match bs with
       | [b] -> b
       | _ -> raise_error (Fatal_SyntaxError, "Syntax error: expected a single binder") (rhs parseState 1)
    }

calcRel:
  | i=binop_name { mk_term (Op (i, [])) (rhs parseState 1) Expr }
  | BACKTICK id=qlident BACKTICK { mk_term (Var id) (rhs2 parseState 2 4) Un }
  | t=atomicTerm { t }

calcStep:
   | rel=calcRel LBRACE justif=option(term) RBRACE next=noSeqTerm SEMICOLON
     {
         let justif =
             match justif with
             | Some t -> t
             | None -> mk_term (Const Const_unit) (rhs2 parseState 2 4) Expr
         in
         CalcStep (rel, justif, next)
     }

typ:
  | t=simpleTerm { t }

  | q=quantifier bs=binders DOT trigger=trigger e=noSeqTerm
      {
        match bs with
        | [] ->
          raise_error (Fatal_MissingQuantifierBinder, "Missing binders for a quantifier") (rhs2 parseState 1 3)
        | _ ->
          let idents = idents_of_binders bs (rhs2 parseState 1 3) in
          mk_term (q (bs, (idents, trigger), e)) (rhs2 parseState 1 5) Formula
      }

%inline quantifier:
  | FORALL { fun x -> QForall x }
  | EXISTS { fun x -> QExists x}

trigger:
  |   { [] }
  | LBRACE_COLON_PATTERN pats=disjunctivePats RBRACE { pats }

disjunctivePats:
  | pats=separated_nonempty_list(DISJUNCTION, conjunctivePat) { pats }

conjunctivePat:
  | pats=separated_nonempty_list(SEMICOLON, appTerm)          { pats }

simpleTerm:
  | e=tmIff { e }
  | FUN pats=nonempty_list(patternOrMultibinder) RARROW e=term
      { mk_term (Abs(flatten pats, e)) (rhs2 parseState 1 4) Un }

maybeFocusArrow:
  | RARROW          { false }
  | SQUIGGLY_RARROW { true }

patternBranch:
  | pat=disjunctivePattern when_opt=maybeWhen focus=maybeFocusArrow e=term
      {
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 1)
        in
        (focus, (pat, when_opt, e))
      }

%inline maybeWhen:
  |                      { None }
  | WHEN e=tmFormula     { Some e }



tmIff:
  | e1=tmImplies IFF e2=tmIff
      { mk_term (Op(mk_ident("<==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula }
  | e=tmImplies { e }

tmImplies:
  | e1=tmArrow(tmFormula) IMPLIES e2=tmImplies
      { mk_term (Op(mk_ident("==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula }
  | e=tmArrow(tmFormula)
      { e }


(* Tm : either tmFormula, containing EQUALS or tmNoEq, without EQUALS *)
tmArrow(Tm):
  | dom=tmArrowDomain(Tm) RARROW tgt=tmArrow(Tm)
     {
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     }
  | e=Tm { e }

simpleArrow:
  | dom=simpleArrowDomain RARROW tgt=simpleArrow
     {
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rhs parseState 1) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     }
  | e=tmEqNoRefinement { e }

simpleArrowDomain:
  | LBRACE_BAR t=tmEqNoRefinement BAR_RBRACE { ((Some TypeClassArg, []), t) }
  | aq_opt=ioption(aqual) attrs_opt=ioption(binderAttributes) dom_tm=tmEqNoRefinement { (aq_opt, none_to_empty_list attrs_opt), dom_tm }

(* Tm already account for ( term ), we need to add an explicit case for (#Tm) *)
%inline tmArrowDomain(Tm):
  | LBRACE_BAR t=Tm BAR_RBRACE { ((Some TypeClassArg, []), t) }
  | LPAREN q=aqual attrs_opt=ioption(binderAttributes) dom_tm=Tm RPAREN { (Some q, none_to_empty_list attrs_opt), dom_tm }
  | aq_opt=ioption(aqual) attrs_opt=ioption(binderAttributes) dom_tm=Tm { (aq_opt, none_to_empty_list attrs_opt), dom_tm }

tmFormula:
  | e1=tmFormula DISJUNCTION e2=tmConjunction
      { mk_term (Op(mk_ident("\\/", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula }
  | e=tmConjunction { e }

tmConjunction:
  | e1=tmConjunction CONJUNCTION e2=tmTuple
      { mk_term (Op(mk_ident("/\\", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula }
  | e=tmTuple { e }

tmTuple:
  | el=separated_nonempty_list(COMMA, tmEq)
      {
        match el with
          | [x] -> x
          | components -> mkTuple components (rhs2 parseState 1 1)
      }


tmEqWith(X):
  | e1=tmEqWith(X) EQUALS e2=tmEqWith(X)
      { mk_term (Op(mk_ident("=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  (* non-associativity of COLON_EQUALS is currently not well handled by fsyacc which reports a s/r conflict *)
  (* see https:/ /github.com/fsprojects/FsLexYacc/issues/39 *)
  | e1=tmEqWith(X) COLON_EQUALS e2=tmEqWith(X)
      { mk_term (Op(mk_ident(":=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  | e1=tmEqWith(X) PIPE_RIGHT e2=tmEqWith(X)
      { mk_term (Op(mk_ident("|>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  | e1=tmEqWith(X) op=operatorInfix0ad12 e2=tmEqWith(X)
      { mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un}
  | e1=tmEqWith(X) MINUS e2=tmEqWith(X)
      { mk_term (Op(mk_ident("-", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  | MINUS e=tmEqWith(X)
      { mk_uminus e (rhs parseState 1) (rhs2 parseState 1 2) Expr }
  | QUOTE e=tmEqWith(X)
      { mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un }
  | BACKTICK e=tmEqWith(X)
      { mk_term (Quote (e, Static)) (rhs2 parseState 1 3) Un }
  | BACKTICK_AT e=atomicTerm
      { let q = mk_term (Quote (e, Dynamic)) (rhs2 parseState 1 3) Un in
        mk_term (Antiquote q) (rhs2 parseState 1 3) Un }
  | BACKTICK_HASH e=atomicTerm
      { mk_term (Antiquote e) (rhs2 parseState 1 3) Un }
  | e=tmNoEqWith(X)
      { e }

tmNoEqWith(X):
  | e1=tmNoEqWith(X) COLON_COLON e2=tmNoEqWith(X)
      { consTerm (rhs parseState 2) e1 e2 }
  | e1=tmNoEqWith(X) AMP e2=tmNoEqWith(X)
      {
            let dom =
               match extract_named_refinement e1 with
               | Some (x, t, f) ->
                 let dom = mkRefinedBinder x t true f (rhs parseState 1) None [] in
                 Inl dom
               | _ ->
                 Inr e1
            in
            let tail = e2 in
            let dom, res =
                match tail.tm with
                | Sum(dom', res) -> dom::dom', res
                | _ -> [dom], tail
            in
            mk_term (Sum(dom, res)) (rhs2 parseState 1 3) Type_level
      }
  | e1=tmNoEqWith(X) op=OPINFIX3 e2=tmNoEqWith(X)
      { mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  | e1=tmNoEqWith(X) BACKTICK op=tmNoEqWith(X) BACKTICK e2=tmNoEqWith(X)
      { mkApp op [ e1, Infix; e2, Nothing ] (rhs2 parseState 1 5) }
 | e1=tmNoEqWith(X) op=OPINFIX4 e2=tmNoEqWith(X)
      { mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un}
  | LBRACE e=recordExp RBRACE { e }
  | BACKTICK_PERC e=atomicTerm
      { mk_term (VQuote e) (rhs2 parseState 1 3) Un }
  | op=TILDE e=atomicTerm
      { mk_term (Op(mk_ident (op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Formula }
  | e=X { e }

binop_name:
  | o=OPINFIX0a              { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX0b              { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX0c              { mk_ident (o, rhs parseState 1) }
  | o=EQUALS                 { mk_ident ("=", rhs parseState 1) }
  | o=OPINFIX0d              { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX1               { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX2               { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX3               { mk_ident (o, rhs parseState 1) }
  | o=OPINFIX4               { mk_ident (o, rhs parseState 1) }
  | o=IMPLIES                { mk_ident ("==>", rhs parseState 1) }
  | o=CONJUNCTION            { mk_ident ("/\\", rhs parseState 1) }
  | o=DISJUNCTION            { mk_ident ("\\/", rhs parseState 1) }
  | o=IFF                    { mk_ident ("<==>", rhs parseState 1) }
  | o=PIPE_RIGHT             { mk_ident ("|>", rhs parseState 1) }
  | o=COLON_EQUALS           { mk_ident (":=", rhs parseState 1) }
  | o=COLON_COLON            { mk_ident ("::", rhs parseState 1) }
  | o=OP_MIXFIX_ASSIGNMENT   { mk_ident (o, rhs parseState 1) }
  | o=OP_MIXFIX_ACCESS       { mk_ident (o, rhs parseState 1) }

tmEqNoRefinement:
  | e=tmEqWith(appTermNoRecordExp) { e }

tmEq:
  | e=tmEqWith(tmRefinement)  { e }

tmNoEq:
  | e=tmNoEqWith(tmRefinement) { e }

tmRefinement:
  | id=lidentOrUnderscore COLON e=appTermNoRecordExp phi_opt=refineOpt
      {
        let t = match phi_opt with
          | None -> NamedTyp(id, e)
          | Some phi -> Refine(mk_binder (Annotated(id, e)) (rhs2 parseState 1 3) Type_level None, phi)
        in mk_term t (rhs2 parseState 1 4) Type_level
      }
  | e=appTerm  { e }

refineOpt:
  | phi_opt=option(LBRACE phi=formula RBRACE {phi}) {phi_opt}

%inline formula:
  | e=noSeqTerm { {e with level=Formula} }

recordExp:
  | record_fields=right_flexible_nonempty_list(SEMICOLON, simpleDef)
      { mk_term (Record (None, record_fields)) (rhs parseState 1) Expr }
  | e=appTerm WITH  record_fields=right_flexible_nonempty_list(SEMICOLON, simpleDef)
      { mk_term (Record (Some e, record_fields)) (rhs2 parseState 1 3) Expr }

simpleDef:
  | e=separated_pair(qlidentOrOperator, EQUALS, noSeqTerm) { e }
  | lid=qlidentOrOperator { lid, mk_term (Name (lid_of_ids [ ident_of_lid lid ])) (rhs parseState 1) Un }

%inline appTermCommon(argTerm):
  | head=indexingTerm args=list(argTerm)
      { mkApp head (map (fun (x,y) -> (y,x)) args) (rhs2 parseState 1 2) }

appTerm:
  | t=appTermCommon(t=argTerm {t} | h=maybeHash LBRACE t=recordExp RBRACE {h, t}) {t}

appTermNoRecordExp:
  | t=appTermCommon(argTerm) {t}

argTerm:
  | x=pair(maybeHash, indexingTerm) { x }
  | u=universe { u }

%inline maybeHash:
  |      { Nothing }
  | HASH { Hash }

indexingTerm:
  | e1=atomicTermNotQUident op_exprs=nonempty_list(dotOperator)
      {
        List.fold_left (fun e1 (op, e2, r) ->
            mk_term (Op(op, [ e1; e2 ])) (union_ranges e1.range r) Expr)
            e1 op_exprs
      }
  | e=atomicTerm
    { e }

atomicTerm:
  | x=atomicTermNotQUident
    { x }
  | x=atomicTermQUident
    { x }
  | x=opPrefixTerm(atomicTermQUident)
    { x }

atomicTermQUident:
  | id=quident
    {
        let t = Name id in
        let e = mk_term t (rhs parseState 1) Un in
              e
    }
  | id=quident DOT_LPAREN t=term RPAREN
    {
      mk_term (LetOpen (id, t)) (rhs2 parseState 1 4) Expr
    }

atomicTermNotQUident:
  | UNDERSCORE { mk_term Wild (rhs parseState 1) Un }
  | tv=tvar     { mk_term (Tvar tv) (rhs parseState 1) Type_level }
  | c=constant { mk_term (Const c) (rhs parseState 1) Expr }
  | x=opPrefixTerm(atomicTermNotQUident)
    { x }
  | LPAREN op=operator RPAREN
      { mk_term (Op(op, [])) (rhs2 parseState 1 3) Un }
  | LENS_PAREN_LEFT e0=tmEq COMMA el=separated_nonempty_list(COMMA, tmEq) LENS_PAREN_RIGHT
      { mkDTuple (e0::el) (rhs2 parseState 1 5) }
  | e=projectionLHS field_projs=list(DOT id=qlident {id})
      { fold_left (fun e lid -> mk_term (Project(e, lid)) (rhs2 parseState 1 2) Expr ) e field_projs }
  | BEGIN e=term END
      { e }

(* Tm: atomicTermQUident or atomicTermNotQUident *)
opPrefixTerm(Tm):
  | op=OPPREFIX e=Tm
      { mk_term (Op(mk_ident(op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Expr }


projectionLHS:
  | e=qidentWithTypeArgs(qlident, option(fsTypeArgs))
      { e }
  | e=qidentWithTypeArgs(quident, some(fsTypeArgs))
      { e }
  | LPAREN e=term sort_opt=option(pair(hasSort, simpleTerm)) RPAREN
      {
        (* Note: we have to keep the parentheses here. Consider t * u * v. This
         * is parsed as Op2( *, Op2( *, t, u), v). The desugaring phase then looks
         * up * and figures out that it hasn't been overridden, meaning that
         * it's a tuple type, and proceeds to flatten out the whole tuple. Now
         * consider (t * u) * v. We keep the Paren node, which prevents the
         * flattening from happening, hence ensuring the proper type is
         * generated. *)
        let e1 = match sort_opt with
          | None -> e
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level},None,false)) (rhs2 parseState 1 4) level
        in mk_term (Paren e1) (rhs2 parseState 1 4) (e.level)
      }
  | LBRACK_BAR es=semiColonTermList BAR_RBRACK
      {
        let l = mkConsList (rhs2 parseState 1 3) es in
        let pos = (rhs2 parseState 1 3) in
        mkExplicitApp (mk_term (Var (array_of_list_lid)) pos Expr) [l] pos
      }
  | LBRACK es=semiColonTermList RBRACK
      { mkConsList (rhs2 parseState 1 3) es }
  | PERCENT_LBRACK es=semiColonTermList RBRACK
      { mk_term (LexList es) (rhs2 parseState 1 3) Type_level }
  | ns=quident QMARK_DOT id=lident
      { mk_term (Projector (ns, id)) (rhs2 parseState 1 3) Expr }
  | lid=quident QMARK
      { mk_term (Discrim lid) (rhs2 parseState 1 2) Un }

fsTypeArgs:
  | TYP_APP_LESS targs=separated_nonempty_list(COMMA, atomicTerm) TYP_APP_GREATER
    {targs}

(* Qid : quident or qlident.
   TypeArgs : option(fsTypeArgs) or someFsTypeArgs. *)
qidentWithTypeArgs(Qid,TypeArgs):
  | id=Qid targs_opt=TypeArgs
      {
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 2)
      }

hasSort:
  | SUBKIND { Type_level } (* Remove with stratify *)

  (* use flexible_list *)
%inline semiColonTermList:
  | l=right_flexible_list(SEMICOLON, noSeqTerm) { l }

constant:
  | LPAREN_RPAREN { Const_unit }
  | n=INT
     {
        if snd n then
          log_issue (lhs parseState) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        Const_int (fst n, None)
     }
  | c=CHAR { Const_char c }
  | s=STRING { Const_string (s,lhs(parseState)) }
  | TRUE { Const_bool true }
  | FALSE { Const_bool false }
  | r=REAL { Const_real r }
  | n=UINT8 { Const_int (n, Some (Unsigned, Int8)) }
  | n=INT8
      {
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 8-bit signed integers");
        Const_int (fst n, Some (Signed, Int8))
      }
  | n=UINT16 { Const_int (n, Some (Unsigned, Int16)) }
  | n=INT16
      {
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 16-bit signed integers");
        Const_int (fst n, Some (Signed, Int16))
      }
  | n=UINT32 { Const_int (n, Some (Unsigned, Int32)) }
  | n=INT32
      {
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 32-bit signed integers");
        Const_int (fst n, Some (Signed, Int32))
      }
  | n=UINT64 { Const_int (n, Some (Unsigned, Int64)) }
  | n=INT64
      {
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for 64-bit signed integers");
        Const_int (fst n, Some (Signed, Int64))
      }
  | n=SIZET { Const_int (n, Some (Unsigned, Sizet)) }
  (* TODO : What about reflect ? There is also a constant representing it *)
  | REIFY   { Const_reify None }
  | RANGE_OF     { Const_range_of }
  | SET_RANGE_OF { Const_set_range_of }


universe:
  | UNIV_HASH ua=atomicUniverse { (UnivApp, ua) }

universeFrom:
  | ua=atomicUniverse { ua }
  | u1=universeFrom op_plus=OPINFIX2 u2=universeFrom
       {
         if op_plus <> "+"
         then log_issue (rhs parseState 2) (Error_OpPlusInUniverse, ("The operator " ^ op_plus ^ " was found in universe context."
                           ^ "The only allowed operator in that context is +."));
         mk_term (Op(mk_ident (op_plus, rhs parseState 2), [u1 ; u2])) (rhs2 parseState 1 3) Expr
       }
  | max=ident us=nonempty_list(atomicUniverse)
      {
        if string_of_id max <> string_of_lid max_lid
        then log_issue (rhs parseState 1) (Error_InvalidUniverseVar, "A lower case ident " ^ string_of_id max ^
                          " was found in a universe context. " ^
                          "It should be either max or a universe variable 'usomething.");
        let max = mk_term (Var (lid_of_ids [max])) (rhs parseState 1) Expr in
        mkApp max (map (fun u -> u, Nothing) us) (rhs2 parseState 1 2)
      }

atomicUniverse:
  | UNDERSCORE
      { mk_term Wild (rhs parseState 1) Expr }
  | n=INT
      {
        if snd n then
          log_issue (lhs(parseState)) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        mk_term (Const (Const_int (fst n, None))) (rhs parseState 1) Expr
      }
  | u=lident { mk_term (Uvar u) (range_of_id u) Expr }
  | LPAREN u=universeFrom RPAREN
    { u (*mk_term (Paren u) (rhs2 parseState 1 3) Expr*) }

/******************************************************************************/
/*                       Miscellanous, tools                                   */
/******************************************************************************/

%inline operator:
  | op=OPPREFIX
    { mk_ident (op, rhs parseState 1) }
  | op=binop_name
    { op }
  | op=TILDE
    { mk_ident (op, rhs parseState 1) }
  | op=and_op       {op}
  | op=let_op       {op}

%inline and_op:
  | op=AND_OP { mk_ident ("and" ^ op, rhs parseState 1) }
%inline let_op:
  | op=LET_OP { mk_ident ("let" ^ op, rhs parseState 1) }

/* These infix operators have a lower precedence than EQUALS */
%inline operatorInfix0ad12:
  | op=OPINFIX0a
  | op=OPINFIX0b
  | op=OPINFIX0c
  | op=OPINFIX0d
  | op=OPINFIX1
  | op=OPINFIX2
     { mk_ident (op, rhs parseState 1) }

%inline dotOperator:
  | DOT_LPAREN e=term RPAREN { mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 }
  | DOT_LBRACK e=term RBRACK { mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 }
  | DOT_LBRACK_BAR e=term BAR_RBRACK { mk_ident (".[||]", rhs parseState 1), e, rhs2 parseState 1 3 }
  | DOT_LENS_PAREN_LEFT e=term LENS_PAREN_RIGHT { mk_ident (".(||)", rhs parseState 1), e, rhs2 parseState 1 3 }

some(X):
  | x=X { Some x }

right_flexible_list(SEP, X):
  |     { [] }
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

right_flexible_nonempty_list(SEP, X):
  | x=X { [x] }
  | x=X SEP xs=right_flexible_list(SEP, X) { x :: xs }

reverse_left_flexible_list(delim, X):
| (* nothing *)
   { [] }
| x = X
   { [x] }
| xs = reverse_left_flexible_list(delim, X) delim x = X
   { x :: xs }

%inline left_flexible_list(delim, X):
 xs = reverse_left_flexible_list(delim, X)
   { List.rev xs }

reverse_left_flexible_nonempty_list(delim, X):
| ioption(delim) x = X
   { [x] }
| xs = reverse_left_flexible_nonempty_list(delim, X) delim x = X
   { x :: xs }

%inline left_flexible_nonempty_list(delim, X):
 xs = reverse_left_flexible_nonempty_list(delim, X)
   { List.rev xs }

attribute:
  | LBRACK_AT x = list(atomicTerm) RBRACK
      {
        let _ =
            match x with
            | _::_::_ ->
                  log_issue (lhs parseState) (Warning_DeprecatedAttributeSyntax,
                                              old_attribute_syntax_warning)
            | _ -> () in
         x
      }
  | LBRACK_AT_AT x = semiColonTermList RBRACK
      { x }

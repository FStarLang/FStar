%{
(*
 We are expected to have only 6 shift-reduce conflicts in ML and 8 in F#.
 A lot (176) of end-of-stream conflicts are also reported and
 should be investigated...
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Prims
open FStar_Errors
open FStar_List
open FStar_Util
open FStar_Range
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

let logic_qualifier_deprecation_warning =
  "logic qualifier is deprecated, please remove it from the source program. In case your program verifies with the qualifier annotated but not without it, please try to minimize the example and file a github issue"

%}

%token <bytes> BYTEARRAY
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
%token <float> IEEE64
%token <string> REAL
%token <char> CHAR
%token <bool> LET
%token <FStar_Parser_AST.fsdoc> FSDOC
%token <FStar_Parser_AST.fsdoc> FSDOC_STANDALONE

%token FORALL EXISTS ASSUME NEW LOGIC ATTRIBUTES
%token IRREDUCIBLE UNFOLDABLE INLINE OPAQUE ABSTRACT UNFOLD INLINE_FOR_EXTRACTION
%token NOEXTRACT
%token NOEQUALITY UNOPTEQUALITY PRAGMALIGHT PRAGMA_SET_OPTIONS PRAGMA_RESET_OPTIONS PRAGMA_PUSH_OPTIONS PRAGMA_POP_OPTIONS PRAGMA_RESTART_SOLVER
%token TYP_APP_LESS TYP_APP_GREATER SUBTYPE SUBKIND BY
%token AND ASSERT SYNTH BEGIN ELSE END
%token EXCEPTION FALSE FUN FUNCTION IF IN MODULE DEFAULT
%token MATCH OF
%token FRIEND OPEN REC THEN TRUE TRY TYPE CALC CLASS INSTANCE EFFECT VAL
%token INCLUDE
%token WHEN WITH HASH AMP LPAREN RPAREN LPAREN_RPAREN COMMA LONG_LEFT_ARROW LARROW RARROW
%token IFF IMPLIES CONJUNCTION DISJUNCTION
%token DOT COLON COLON_COLON SEMICOLON
%token QMARK_DOT
%token QMARK
%token SEMICOLON_SEMICOLON EQUALS PERCENT_LBRACK LBRACK_AT DOT_LBRACK DOT_LENS_PAREN_LEFT DOT_LPAREN DOT_LBRACK_BAR LBRACK LBRACK_BAR LBRACE BANG_LBRACE
%token BAR_RBRACK UNDERSCORE LENS_PAREN_LEFT LENS_PAREN_RIGHT
%token BAR RBRACK RBRACE DOLLAR
%token PRIVATE REIFIABLE REFLECTABLE REIFY RANGE_OF SET_RANGE_OF LBRACE_COLON_PATTERN PIPE_RIGHT
%token NEW_EFFECT SUB_EFFECT LAYERED_EFFECT SPLICE SQUIGGLY_RARROW TOTAL
%token REQUIRES ENSURES
%token MINUS COLON_EQUALS QUOTE BACKTICK_AT BACKTICK_HASH
%token BACKTICK UNIV_HASH
%token BACKTICK_PERC

%token<string>  OPPREFIX OPINFIX0a OPINFIX0b OPINFIX0c OPINFIX0d OPINFIX1 OPINFIX2 OPINFIX3 OPINFIX4
%token<string>  OP_MIXFIX_ASSIGNMENT OP_MIXFIX_ACCESS

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
%left     BACKTICK_AT BACKTICK_HASH
%right    OPINFIX4

%start inputFragment
%start term
%start warn_error_list
%type <FStar_Parser_AST.inputFragment> inputFragment
%type <FStar_Parser_AST.term> term
%type <FStar_Ident.ident> lident
%type <(FStar_Errors.flag * string) list> warn_error_list
%%

(* inputFragment is used at the same time for whole files and fragment of codes (for interactive mode) *)
inputFragment:
  | is_light=boption(PRAGMALIGHT STRING { }) decls=list(decl) EOF
      {
        as_frag is_light (rhs parseState 1) decls
      }


/******************************************************************************/
/*                      Top level declarations                                */
/******************************************************************************/

pragma:
  | PRAGMA_SET_OPTIONS s=string
      { SetOptions s }
  | PRAGMA_RESET_OPTIONS s_opt=string?
      { ResetOptions s_opt }
  | PRAGMA_PUSH_OPTIONS s_opt=string?
      { PushOptions s_opt }
  | PRAGMA_POP_OPTIONS
      { PopOptions }
  | PRAGMA_RESTART_SOLVER
      { RestartSolver }

attribute:
  | LBRACK_AT x = list(atomicTerm) RBRACK
      { x }

decoration:
  | x=FSDOC
      { Doc x }
  | x=attribute
      { DeclAttributes x }
  | x=qualifier
      { Qualifier x }

decl:
  | ASSUME lid=uident COLON phi=formula
      { mk_decl (Assume(lid, phi)) (rhs2 parseState 1 4) [ Qualifier Assumption ] }

  | ds=list(decoration) decl=rawDecl
      { mk_decl decl (rhs parseState 2) ds }

  | ds=list(decoration) decl=typeclassDecl
      { let (decl, extra_attrs) = decl in
        let d = mk_decl decl (rhs parseState 2) ds in
        { d with attrs = extra_attrs @ d.attrs }
      }

typeclassDecl:
  | CLASS tcdef=pair(option(FSDOC), typeDecl)
      {
        (* Only a single type decl allowed, but construct it the same as for multiple ones.
         * Only difference is the `true` below marking that this a class so desugaring
         * adds the needed %splice. *)
        let flip (a,b) = (b,a) in
        let tcdef = flip tcdef in
        let d = Tycon (false, true, [tcdef]) in

        (* No attrs yet, but perhaps we want a `class` attribute *)
        (d, [])
      }

  | INSTANCE q=letqualifier lb=letbinding
      {
        (* Making a single letbinding *)
        let r = rhs2 parseState 1 3 in
        let lbs = focusLetBindings [lb] r in (* lbs is a singleton really *)
        let d = TopLevelLet(q, lbs) in

        (* Slapping a `tcinstance` attribute to it *)
        let at = mk_term (Var tcinstance_lid) r Type_level in

        (d, [at])
      }

rawDecl:
  | p=pragma
      { Pragma p }
  | OPEN uid=quident
      { Open uid }
  | FRIEND uid=quident
      { Friend uid }
  | INCLUDE uid=quident
      { Include uid }
  | MODULE uid1=uident EQUALS uid2=quident
      { ModuleAbbrev(uid1, uid2) }
  | MODULE uid=quident
      {  TopLevelModule uid }
  | TYPE tcdefs=separated_nonempty_list(AND,pair(option(FSDOC), typeDecl))
      { Tycon (false, false, List.map (fun (doc, f) -> (f, doc)) tcdefs) }
  | EFFECT uid=uident tparams=typars EQUALS t=typ
      { Tycon(true, false, [(TyconAbbrev(uid, tparams, None, t), None)]) }
  | LET q=letqualifier lbs=separated_nonempty_list(AND, letbinding)
      {
        let r = rhs2 parseState 1 3 in
        let lbs = focusLetBindings lbs r in
        if q <> Rec && List.length lbs <> 1
        then raise_error (Fatal_MultipleLetBinding, "Unexpected multiple let-binding (Did you forget some rec qualifier ?)") r;
        TopLevelLet(q, lbs)
      }
  | VAL lid=lidentOrOperator bss=list(multiBinder) COLON t=typ
      {
        let t = match flatten bss with
          | [] -> t
          | bs -> mk_term (Product(bs, t)) (rhs2 parseState 3 5) Type_level
        in Val(lid, t)
      }
  | SPLICE LBRACK ids=separated_list(SEMICOLON, lidentOrOperator) RBRACK t=thunk(atomicTerm)
      { Splice (ids, t) }
  | EXCEPTION lid=uident t_opt=option(OF t=typ {t})
      { Exception(lid, t_opt) }
  | NEW_EFFECT ne=newEffect
      { NewEffect ne }
  | LAYERED_EFFECT ne=effectDefinition
      { LayeredEffect ne }
  | SUB_EFFECT se=subEffect
      { SubEffect se }
  | doc=FSDOC_STANDALONE
      { Fsdoc doc }

typeDecl:
  (* TODO : change to lident with stratify *)
  | lid=ident tparams=typars ascr_opt=ascribeKind? tcdef=typeDefinition
      { tcdef lid tparams ascr_opt }

typars:
  | x=tvarinsts              { x }
  | x=binders                { x }

tvarinsts:
  | TYP_APP_LESS tvs=separated_nonempty_list(COMMA, tvar) TYP_APP_GREATER
      { map (fun tv -> mk_binder (TVariable(tv)) tv.idRange Kind None) tvs }

typeDefinition:
  |   { (fun id binders kopt -> check_id id; TyconAbstract(id, binders, kopt)) }
  | EQUALS t=typ
      { (fun id binders kopt ->  check_id id; TyconAbbrev(id, binders, kopt, t)) }
  /* A documentation on the first branch creates a conflict with { x with a = ... }/{ a = ... } */
  | EQUALS LBRACE
      record_field_decls=right_flexible_nonempty_list(SEMICOLON, recordFieldDecl)
   RBRACE
      { (fun id binders kopt -> check_id id; TyconRecord(id, binders, kopt, record_field_decls)) }
  (* having the first BAR optional using left-flexible list creates a s/r on FSDOC since any decl can be preceded by a FSDOC *)
  | EQUALS ct_decls=list(constructorDecl)
      { (fun id binders kopt -> check_id id; TyconVariant(id, binders, kopt, ct_decls)) }

recordFieldDecl:
  |  doc_opt=ioption(FSDOC) lid=lident COLON t=typ
      { (lid, t, doc_opt) }

constructorDecl:
  | BAR doc_opt=FSDOC? uid=uident COLON t=typ                { (uid, Some t, doc_opt, false) }
  | BAR doc_opt=FSDOC? uid=uident t_opt=option(OF t=typ {t}) { (uid, t_opt, doc_opt, true) }

attr_letbinding:
  | attr=ioption(attribute) AND lb=letbinding
    { attr, lb }

letbinding:
  | focus_opt=maybeFocus lid=lidentOrOperator lbp=nonempty_list(patternOrMultibinder) ascr_opt=ascribeTyp? EQUALS tm=term
      {
        let pat = mk_pattern (PatVar(lid, None)) (rhs parseState 2) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rhs2 parseState 1 3) in
        let pos = rhs2 parseState 1 6 in
        match ascr_opt with
        | None -> (focus_opt, (pat, tm))
        | Some t -> (focus_opt, (mk_pattern (PatAscribed(pat, t)) pos, tm))
      }
  | focus_opt=maybeFocus pat=tuplePattern ascr=ascribeTyp EQUALS tm=term
      { focus_opt, (mk_pattern (PatAscribed(pat, ascr)) (rhs2 parseState 1 4), tm) }
  | focus_opt=maybeFocus pat=tuplePattern EQUALS tm=term
      { focus_opt, (pat, tm) }

/******************************************************************************/
/*                                Effects                                     */
/******************************************************************************/

newEffect:
  | ed=effectRedefinition
  | ed=effectDefinition
    { ed }

effectRedefinition:
  | lid=uident EQUALS t=simpleTerm
    { RedefineEffect(lid, [], t) }

effectDefinition:
  | LBRACE lid=uident bs=binders COLON typ=tmArrow(tmNoEq)
           WITH eds=separated_nonempty_list(SEMICOLON, effectDecl)
    RBRACE
    { DefineEffect(lid, bs, typ, eds) }

effectDecl:
  | lid=lident action_params=binders EQUALS t=simpleTerm
    { mk_decl (Tycon (false, false, [TyconAbbrev(lid, action_params, None, t), None])) (rhs2 parseState 1 3) [] }

subEffect:
  | src_eff=quident SQUIGGLY_RARROW tgt_eff=quident EQUALS lift=simpleTerm
      { { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift } }
  | src_eff=quident SQUIGGLY_RARROW tgt_eff=quident
    LBRACE
      lift1=separated_pair(IDENT, EQUALS, simpleTerm)
      lift2_opt=ioption(separated_pair(SEMICOLON id=IDENT {id}, EQUALS, simpleTerm))
      /* might be nice for homogeneity if possible : ioption(SEMICOLON) */
    RBRACE
     {
       match lift2_opt with
       | None ->
          begin match lift1 with
          | ("lift", lift) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp }
          | _ ->
             raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', and possibly 'lift_wp'}") (lhs parseState)
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', 'lift_wp'}") (lhs parseState)
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp) }
     }


/******************************************************************************/
/*                        Qualifiers, tags, ...                               */
/******************************************************************************/

qualifier:
  | ASSUME        { Assumption }
  | INLINE        {
    raise_error (Fatal_InlineRenamedAsUnfold, "The 'inline' qualifier has been renamed to 'unfold'") (lhs parseState)
   }
  | UNFOLDABLE    {
              raise_error (Fatal_UnfoldableDeprecated, "The 'unfoldable' qualifier is no longer denotable; it is the default qualifier so just omit it") (lhs parseState)
   }
  | INLINE_FOR_EXTRACTION {
     Inline_for_extraction
  }
  | UNFOLD {
     Unfold_for_unification_and_vcgen
  }
  | IRREDUCIBLE   { Irreducible }
  | NOEXTRACT     { NoExtract }
  | DEFAULT       { DefaultEffect }
  | TOTAL         { TotalEffect }
  | PRIVATE       { Private }
  | ABSTRACT      { Abstract }
  | NOEQUALITY    { Noeq }
  | UNOPTEQUALITY { Unopteq }
  | NEW           { New }
  | LOGIC         { log_issue (lhs parseState) (Warning_logicqualifier,
                                                logic_qualifier_deprecation_warning);
                    Logic }
  | OPAQUE        { Opaque }
  | REIFIABLE     { Reifiable }
  | REFLECTABLE   { Reflectable }

maybeFocus:
  | b=boption(SQUIGGLY_RARROW) { b }

letqualifier:
  | REC         { Rec }
  |             { NoLetQualifier }

 (* Remove with stratify *)
aqual:
  | EQUALS    {  log_issue (lhs parseState) (Warning_DeprecatedEqualityOnBinder, "The '=' notation for equality constraints on binders is deprecated; use '$' instead");
                                        Equality }
  | q=aqualUniverses { q }

aqualUniverses:
  | HASH LBRACK t=thunk(tmNoEq) RBRACK { Meta t }
  | HASH      { Implicit }
  | DOLLAR    { Equality }

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
  | tv=tvar                   { mk_pattern (PatTvar (tv, None)) (rhs parseState 1) }
  | LPAREN op=operator RPAREN
      { mk_pattern (PatOp op) (rhs2 parseState 1 3) }
  | UNDERSCORE
      { mk_pattern (PatWild None) (rhs parseState 1) }
  | HASH UNDERSCORE
      { mk_pattern (PatWild (Some Implicit)) (rhs parseState 1) }
  | c=constant
      { mk_pattern (PatConst c) (rhs parseState 1) }
  | qual_id=aqualified(lident)
      { mk_pattern (PatVar (snd qual_id, fst qual_id)) (rhs parseState 1) }
  | uid=quident
      { mk_pattern (PatName uid) (rhs parseState 1) }

fieldPattern:
  | p = separated_pair(qlident, EQUALS, tuplePattern)
      { p }
  | lid=qlident
      { lid, mk_pattern (PatVar (lid.ident, None)) (rhs parseState 1) }

  (* (x : t) is already covered by atomicPattern *)
  (* we do *NOT* allow _ in multibinder () since it creates reduce/reduce conflicts when*)
  (* preprocessing to ocamlyacc/fsyacc (which is expected since the macro are expanded) *)
patternOrMultibinder:
  | LBRACK_BAR UNDERSCORE COLON t=simpleArrow BAR_RBRACK
      { let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        let w = mk_pattern (PatWild (Some (Meta mt)))
                                 (rhs2 parseState 1 5) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 5)]
      }

  | LBRACK_BAR i=lident COLON t=simpleArrow BAR_RBRACK
      { let mt = mk_term (Var tcresolve_lid) (rhs parseState 4) Type_level in
        let w = mk_pattern (PatVar (i, Some (Meta mt)))
                                 (rhs2 parseState 1 5) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 5)]
      }

  | LBRACK_BAR t=simpleArrow BAR_RBRACK
      { let mt = mk_term (Var tcresolve_lid) (rhs parseState 2) Type_level in
        let w = mk_pattern (PatVar (gen (rhs2 parseState 1 3), Some (Meta mt)))
                                 (rhs2 parseState 1 3) in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) (rhs2 parseState 1 3)]
      }
  | pat=atomicPattern { [pat] }
  | LPAREN qual_id0=aqualified(lident) qual_ids=nonempty_list(aqualified(lident)) COLON t=simpleArrow r=refineOpt RPAREN
      {
        let pos = rhs2 parseState 1 7 in
        let t_pos = rhs parseState 5 in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun (q, x) -> mkRefinedPattern (mk_pattern (PatVar (x, q)) pos) t false r t_pos pos) qual_ids
      }

binder:
  | aqualified_lid=aqualified(lidentOrUnderscore)
     {
       let (q, lid) = aqualified_lid in
       mk_binder (Variable lid) (rhs parseState 1) Type_level q
     }
  | tv=tvar  { mk_binder (TVariable tv) (rhs parseState 1) Kind None  }
       (* small regression here : fun (=x : t) ... is not accepted anymore *)

multiBinder:
  | LPAREN qual_ids=nonempty_list(aqualified(lidentOrUnderscore)) COLON t=simpleArrow r=refineOpt RPAREN
     {
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun (q, x) -> mkRefinedBinder x t should_bind_var r (rhs2 parseState 1 6) q) qual_ids
     }

binders: bss=list(b=binder {[b]} | bs=multiBinder {bs}) { flatten bss }

aqualified(X): x=pair(ioption(aqualUniverses), X) { x }

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

lidentOrOperator:
  | id=IDENT
    { mk_ident(id, rhs parseState 1) }
  | LPAREN id=operator RPAREN
    { {id with idText = compile_op' id.idText id.idRange} }

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

thunk(X): | t=X { mk_term (Abs ([mk_pattern (PatWild None) (rhs parseState 3)], t)) (rhs parseState 3) Expr }

thunk2(X):
  | t=X
     { let u = mk_term (Const Const_unit) (rhs parseState 3) Expr in
       let t = mk_term (Seq (u, t)) (rhs parseState 3) Expr in
       mk_term (Abs ([mk_pattern (PatWild None) (rhs parseState 3)], t)) (rhs parseState 3) Expr }

ascribeTyp:
  | COLON t=tmArrow(tmNoEq) tacopt=option(BY tactic=thunk(atomicTerm) {tactic}) { t, tacopt }

(* Remove for stratify *)
ascribeKind:
  | COLON  k=kind { k }

(* Remove for stratify *)
kind:
  | t=tmArrow(tmNoEq) { {t with level=Kind} }






term:
  | e=noSeqTerm
      { e }
  | e1=noSeqTerm SEMICOLON e2=term
      { mk_term (Seq(e1, e2)) (rhs2 parseState 1 3) Expr }
(* Added this form for sequencing; *)
(* but it results in an additional shift/reduce conflict *)
(* ... which is actually be benign, since the same conflict already *)
(*     exists for the previous production *)
  | e1=noSeqTerm SEMICOLON_SEMICOLON e2=term
      { mk_term (Bind(gen (rhs parseState 2), e1, e2)) (rhs2 parseState 1 3) Expr }
  | x=lidentOrUnderscore LONG_LEFT_ARROW e1=noSeqTerm SEMICOLON e2=term
      { mk_term (Bind(x, e1, e2)) (rhs2 parseState 1 5) Expr }

noSeqTerm:
  | t=typ  { t }
  | e=tmIff SUBTYPE t=tmIff tactic_opt=option(BY tactic=thunk(typ) {tactic})
      { mk_term (Ascribed(e,{t with level=Expr},tactic_opt)) (rhs2 parseState 1 4) Expr }
  | e1=atomicTermNotQUident op_expr=dotOperator LARROW e3=noSeqTerm
      {
        let (op, e2, _) = op_expr in
        mk_term (Op({op with idText = op.idText ^ "<-"}, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      }
  | REQUIRES t=typ
      { mk_term (Requires(t, None)) (rhs2 parseState 1 2) Type_level }
  | ENSURES t=typ
      { mk_term (Ensures(t, None)) (rhs2 parseState 1 2) Type_level }
  | ATTRIBUTES es=nonempty_list(atomicTerm)
      { mk_term (Attributes es) (rhs2 parseState 1 2) Type_level }
  | IF e1=noSeqTerm THEN e2=noSeqTerm ELSE e3=noSeqTerm
      { mk_term (If(e1, e2, e3)) (rhs2 parseState 1 6) Expr }
  | IF e1=noSeqTerm THEN e2=noSeqTerm
      {
        let e3 = mk_term (Const Const_unit) (rhs2 parseState 4 4) Expr in
        mk_term (If(e1, e2, e3)) (rhs2 parseState 1 4) Expr
      }
  | TRY e1=term WITH pbs=left_flexible_nonempty_list(BAR, patternBranch)
      {
         let branches = focusBranches (pbs) (rhs2 parseState 1 4) in
         mk_term (TryWith(e1, branches)) (rhs2 parseState 1 4) Expr
      }
  | MATCH e=term WITH pbs=left_flexible_list(BAR, pb=patternBranch {pb})
      {
        let branches = focusBranches pbs (rhs2 parseState 1 4) in
        mk_term (Match(e, branches)) (rhs2 parseState 1 4) Expr
      }
  | LET OPEN uid=quident IN e=term
      { mk_term (LetOpen(uid, e)) (rhs2 parseState 1 5) Expr }
  | attrs=ioption(attribute)
    LET q=letqualifier lb=letbinding lbs=list(attr_letbinding) IN e=term
      {
        let lbs = (attrs, lb)::lbs in
        let lbs = focusAttrLetBindings lbs (rhs2 parseState 2 3) in
        mk_term (Let(q, lbs, e)) (rhs2 parseState 1 6) Expr
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

   | CALC rel=atomicTerm LBRACE init=noSeqTerm SEMICOLON steps=nonempty_list(calcStep) RBRACE
     {
         mk_term (CalcProof (rel, init, steps)) (rhs2 parseState 1 6) Expr
     }

calcStep:
   | rel=binop LBRACE justif=option(term) RBRACE next=noSeqTerm SEMICOLON
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
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     }
  | e=Tm { e }

simpleArrow:
  | dom=simpleArrowDomain RARROW tgt=simpleArrow
     {
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     }
  | e=tmEqNoRefinement { e }

simpleArrowDomain:
  | aq_opt=ioption(aqual) dom_tm=tmEqNoRefinement { aq_opt, dom_tm }

(* Tm already account for ( term ), we need to add an explicit case for (#Tm) *)
%inline tmArrowDomain(Tm):
  | LPAREN q=aqual dom_tm=Tm RPAREN { Some q, dom_tm }
  | aq_opt=ioption(aqual) dom_tm=Tm { aq_opt, dom_tm }

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
                 let dom = mkRefinedBinder x t true f (rhs parseState 1) None in
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

binop:
  | o=OPINFIX0a { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX0b { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX0c { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=EQUALS    { let i = mk_ident ("=", rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX0d { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX1  { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX2  { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX3  { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | o=OPINFIX4  { let i = mk_ident (o, rhs parseState 1) in mk_term (Op (i, [])) (rhs parseState 2) Expr }
  | BACKTICK id=qlident BACKTICK { mk_term (Var id) (rhs2 parseState 2 4) Un }
  | t=atomicTerm { t }


tmEqNoRefinement:
  | e=tmEqWith(appTerm) { e }

tmEq:
  | e=tmEqWith(tmRefinement)  { e }

tmNoEq:
  | e=tmNoEqWith(tmRefinement) { e }

tmRefinement:
  | id=lidentOrUnderscore COLON e=appTerm phi_opt=refineOpt
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
  | e=separated_pair(qlident, EQUALS, noSeqTerm) { e }
  | lid=qlident { lid, mk_term (Name (lid_of_ids [ lid.ident ])) (rhs parseState 1) Un }

appTerm:
  | head=indexingTerm args=list(argTerm)
      { mkApp head (map (fun (x,y) -> (y,x)) args) (rhs2 parseState 1 2) }

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
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level},None)) (rhs2 parseState 1 4) level
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
      { mkLexList (rhs2 parseState 1 3) es }
  | BANG_LBRACE es=separated_list(COMMA, appTerm) RBRACE
      { mkRefSet (rhs2 parseState 1 3) es }
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
  (* | SUBTYPE { Expr } *)
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
  | bs=BYTEARRAY { Const_bytearray (bs,lhs(parseState)) }
  | TRUE { Const_bool true }
  | FALSE { Const_bool false }
  | r=REAL { Const_real r }
  | f=IEEE64 { Const_float f }
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
  (* TODO : What about reflect ? There is also a constant representing it *)
  | REIFY   { Const_reify }
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
        if text_of_id max <> text_of_lid max_lid
        then log_issue (rhs parseState 1) (Error_InvalidUniverseVar, "A lower case ident " ^ text_of_id max ^
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
  | u=lident { mk_term (Uvar u) u.idRange Expr }
  | LPAREN u=universeFrom RPAREN
    { u (*mk_term (Paren u) (rhs2 parseState 1 3) Expr*) }

warn_error_list:
  | e=warn_error EOF { e }

warn_error:
  | f=flag r=range
    { [(f, r)] }
  | f=flag r=range e=warn_error
    { (f, r) :: e }

flag:
  | op=OPINFIX1
    { if op = "@" then CAlwaysError else failwith (format1 "unexpected token %s in warn-error list" op)}
  | op=OPINFIX2
    { if op = "+" then CWarning else failwith (format1 "unexpected token %s in warn-error list" op)}
  | MINUS
          { CSilent }

range:
  | i=INT
    { format2 "%s..%s" (fst i) (fst i) }
  | r=RANGE
    { r }


/******************************************************************************/
/*                       Miscellanous, tools                                   */
/******************************************************************************/

%inline string:
  | s=STRING { s }

%inline operator:
  | op=OPPREFIX
  | op=OPINFIX3
  | op=OPINFIX4
     { mk_ident (op, rhs parseState 1) }
  | op=operatorInfix0ad12
     { op }
       | op=PIPE_RIGHT
     { mk_ident("|>", rhs parseState 1) }
  | op=COLON_EQUALS
     { mk_ident(":=", rhs parseState 1) }
  | op=COLON_COLON
     { mk_ident("::", rhs parseState 1) }
  | op=OP_MIXFIX_ASSIGNMENT
     { mk_ident(op, rhs parseState 1) }
  | op=OP_MIXFIX_ACCESS
     { mk_ident(op, rhs parseState 1) }

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

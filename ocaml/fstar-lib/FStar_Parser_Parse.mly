%{
(*
 Menhir reports the following warnings:

   Warning: 5 states have shift/reduce conflicts.
   Warning: 6 shift/reduce conflicts were arbitrarily resolved.
   Warning: 222 end-of-stream conflicts were arbitrarily resolved.

 If you're editing this file, be sure to not increase the warnings,
 except if you have a really good reason.

 The shift-reduce conflicts are natural in an ML-style language. E.g.,
 there are S-R conflicts with dangling elses, with a non-delimited match where
 the BAR is dangling etc.

 Note: Some symbols are marked public, so that we can reuse this parser from
 the parser for the Pulse DSL in FStarLang/steel.
 
*)
(* (c) Microsoft Corporation. All rights reserved *)
open Prims
open FStar_Pervasives
open FStar_Errors
open FStar_Compiler_List
open FStar_Compiler_Util
open FStar_Compiler_Range

(* TODO : these files should be deprecated and removed *)
open FStar_Parser_Const
open FStar_Parser_AST
open FStar_Const
open FStar_Ident

(* Shorthands *)
let rr = FStar_Parser_Util.translate_range
let rr2 = FStar_Parser_Util.translate_range2

let logic_qualifier_deprecation_warning =
  "logic qualifier is deprecated, please remove it from the source program. In case your program verifies with the qualifier annotated but not without it, please try to minimize the example and file a github issue"

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

let parse_extension_blob (extension_name:string) (s:string) r : FStar_Parser_AST.decl' =
    DeclSyntaxExtension (extension_name, s, r)
%}

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

%start inputFragment
%start term
%start warn_error_list
%start oneDeclOrEOF
%type <FStar_Parser_AST.inputFragment> inputFragment
%type <FStar_Parser_AST.decl option> oneDeclOrEOF
%type <FStar_Parser_AST.term> term
%type <FStar_Ident.ident> lident
%type <(FStar_Errors_Codes.error_flag * string) list> warn_error_list
%%

(* inputFragment is used at the same time for whole files and fragment of codes (for interactive mode) *)
inputFragment:
  | decls=list(decl) EOF
      {
        as_frag decls
      }

oneDeclOrEOF:
  | EOF { None }
  | d=idecl { Some d }

idecl:
 | d=decl startOfNextDeclToken
     { d }


startOfNextDeclToken:
 | EOF    { () }
 | pragmaStartToken { () }
 | LBRACK_AT { () } (* Attribute start *)
 | LBRACK_AT_AT { () } (* Attribute start *) 
 | qualifier { () }
 | CLASS { () }
 | INSTANCE { () }
 | OPEN  { () }
 | FRIEND  { () }
 | INCLUDE  { () }
 | MODULE  { () }
 | TYPE  { () }
 | EFFECT  { () }
 | LET  { () }
 | VAL  { () }
 | SPLICE  { () }
 | SPLICET  { () }
 | EXCEPTION  { () }
 | NEW_EFFECT  { () }
 | LAYERED_EFFECT  { () }
 | SUB_EFFECT { () }
 | POLYMONADIC_BIND  { () }
 | POLYMONADIC_SUBCOMP  { () }
 
 
pragmaStartToken:
 | PRAGMA_SET_OPTIONS
     { () }
 | PRAGMA_RESET_OPTIONS
     { () }
 | PRAGMA_PUSH_OPTIONS
     { () }
 | PRAGMA_POP_OPTIONS
     { () }
 | PRAGMA_RESTART_SOLVER
     { () }
 | PRAGMA_PRINT_EFFECTS_GRAPH
     { () }

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
  | PRAGMA_PRINT_EFFECTS_GRAPH
      { PrintEffectsGraph }

attribute:
  | LBRACK_AT x = list(atomicTerm) RBRACK
      {
        let _ =
            match x with
            | _::_::_ ->
                  log_issue (rr $loc) (Warning_DeprecatedAttributeSyntax,
                                              old_attribute_syntax_warning)
            | _ -> () in
         x
      }
  | LBRACK_AT_AT x = semiColonTermList RBRACK
      { x }


decoration:
  | x=attribute
      { DeclAttributes x }
  | x=qualifier
      { Qualifier x }

decl:
  | ASSUME lid=uident COLON phi=formula
      { mk_decl (Assume(lid, phi)) (rr $loc) [ Qualifier Assumption ] }

  | ds=list(decoration) decl=rawDecl
      { mk_decl decl (rr $loc(decl)) ds }

  | ds=list(decoration) decl=typeclassDecl
      { let (decl, extra_attrs) = decl in
        let d = mk_decl decl (rr $loc(decl)) ds in
        { d with attrs = extra_attrs @ d.attrs }
      }

typeclassDecl:
  | CLASS tcdef=typeDecl
      {
        (* Only a single type decl allowed, but construct it the same as for multiple ones.
         * Only difference is the `true` below marking that this a class so desugaring
         * adds the needed %splice. *)
        let d = Tycon (false, true, [tcdef]) in

        (* No attrs yet, but perhaps we want a `class` attribute *)
        (d, [])
      }

  | INSTANCE q=letqualifier lb=letbinding
      {
        (* Making a single letbinding *)
        let r = rr $loc in
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
  | MODULE q=qlident
      { raise_error (Fatal_SyntaxError, "Syntax error: expected a module name") (rr $loc(q)) }
  | MODULE uid=quident
      {  TopLevelModule uid }
  | TYPE tcdefs=separated_nonempty_list(AND,typeDecl)
      { Tycon (false, false, tcdefs) }
  | EFFECT uid=uident tparams=typars EQUALS t=typ
      { Tycon(true, false, [(TyconAbbrev(uid, tparams, None, t))]) }
  | LET q=letqualifier lbs=separated_nonempty_list(AND, letbinding)
      {
        let r = rr $loc in
        let lbs = focusLetBindings lbs r in
        if q <> Rec && List.length lbs <> 1
        then raise_error (Fatal_MultipleLetBinding, "Unexpected multiple let-binding (Did you forget some rec qualifier ?)") r;
        TopLevelLet(q, lbs)
      }
  | VAL c=constant
      {
        (* This is just to provide a better error than "syntax error" *)
        raise_error (Fatal_SyntaxError, "Syntax error: constants are not allowed in val declarations") (rr $loc)
      }
  | VAL lid=lidentOrOperator bss=list(multiBinder) COLON t=typ
      {
        let t = match flatten bss with
          | [] -> t
          | bs -> mk_term (Product(bs, t)) (rr2 $loc(bss) $loc(t)) Type_level
        in Val(lid, t)
      }
  | SPLICE LBRACK ids=separated_list(SEMICOLON, ident) RBRACK t=thunk(atomicTerm)
      { Splice (false, ids, t) }
  | SPLICET LBRACK ids=separated_list(SEMICOLON, ident) RBRACK t=atomicTerm
      { Splice (true, ids, t) }
  | EXCEPTION lid=uident t_opt=option(OF t=typ {t})
      { Exception(lid, t_opt) }
  | NEW_EFFECT ne=newEffect
      { NewEffect ne }
  | LAYERED_EFFECT ne=effectDefinition
      { LayeredEffect ne }
  | EFFECT ne=layeredEffectDefinition
      { LayeredEffect ne }
  | SUB_EFFECT se=subEffect
      { SubEffect se }
  | POLYMONADIC_BIND b=polymonadic_bind
      { Polymonadic_bind b }
  | POLYMONADIC_SUBCOMP c=polymonadic_subcomp
      { Polymonadic_subcomp c }
  | blob=BLOB
      {
        let ext_name, contents, pos = blob in
        parse_extension_blob ext_name contents (rr (pos, pos))
      }


typeDecl:
  (* TODO : change to lident with stratify *)
  | lid=ident tparams=typars ascr_opt=ascribeKind? tcdef=typeDefinition
      { tcdef lid tparams ascr_opt }

typars:
  | x=tvarinsts              { x }
  | x=binders                { x }

tvarinsts:
  | TYP_APP_LESS tvs=separated_nonempty_list(COMMA, tvar) TYP_APP_GREATER
      { map (fun tv -> mk_binder (TVariable(tv)) (range_of_id tv) Kind None) tvs }

%inline recordDefinition:
  | LBRACE record_field_decls=right_flexible_nonempty_list(SEMICOLON, recordFieldDecl) RBRACE
    { record_field_decls }

typeDefinition:
  |   { (fun id binders kopt -> check_id id; TyconAbstract(id, binders, kopt)) }
  | EQUALS t=typ
      { (fun id binders kopt ->  check_id id; TyconAbbrev(id, binders, kopt, t)) }
  /* A documentation on the first branch creates a conflict with { x with a = ... }/{ a = ... } */
  | EQUALS attrs_opt=ioption(binderAttributes) record_field_decls=recordDefinition
      { (fun id binders kopt -> check_id id; TyconRecord(id, binders, kopt, none_to_empty_list attrs_opt, record_field_decls)) }
  (* having the first BAR optional using left-flexible list creates a s/r on FSDOC since any decl can be preceded by a FSDOC *)
  | EQUALS ct_decls=list(constructorDecl)
      { (fun id binders kopt -> check_id id; TyconVariant(id, binders, kopt, ct_decls)) }

recordFieldDecl:
  | qualified_lid=aqualifiedWithAttrs(lidentOrOperator) COLON t=typ
      {
        let (qual, attrs), lid = qualified_lid in
        (lid, qual, attrs, t)
      }

constructorPayload:
  | COLON t=typ                                         {VpArbitrary  t}
  |    OF t=typ                                         {VpOfNotation t}
  | fields=recordDefinition opt=option(COLON t=typ {t}) {VpRecord(fields, opt)}

constructorDecl:
  | BAR attrs_opt=ioption(binderAttributes)
        uid=uident
        payload=option(constructorPayload)
    { uid, payload, none_to_empty_list attrs_opt }

attr_letbinding:
  | attr=ioption(attribute) AND lb=letbinding
    { attr, lb }

letoperatorbinding:
  | pat=tuplePattern ascr_opt=ascribeTyp? tm=option(EQUALS tm=term {tm})
    {
        let h tm
	  = ( ( match ascr_opt with
              | None   -> pat
              | Some t -> mk_pattern (PatAscribed(pat, t)) (rr2 $loc(pat) $loc(ascr_opt)) )
	    , tm)
	in
	match pat.pat, tm with
        | _               , Some tm -> h tm
        | PatVar (v, _, _), None    ->
          let v = lid_of_ns_and_id [] v in
          h (mk_term (Var v) (rr $loc(pat)) Expr)
        | _ -> raise_error (Fatal_SyntaxError, "Syntax error: let-punning expects a name, not a pattern") (rr $loc(ascr_opt))
    }

letbinding:
  | focus_opt=maybeFocus lid=lidentOrOperator lbp=nonempty_list(patternOrMultibinder) ascr_opt=ascribeTyp? EQUALS tm=term
      {
        let pat = mk_pattern (PatVar(lid, None, [])) (rr $loc(lid)) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rr2 $loc(focus_opt) $loc(lbp)) in
        let pos = rr2 $loc(focus_opt) $loc(tm) in
        match ascr_opt with
        | None -> (focus_opt, (pat, tm))
        | Some t -> (focus_opt, (mk_pattern (PatAscribed(pat, t)) pos, tm))
      }
  | focus_opt=maybeFocus pat=tuplePattern ascr=ascribeTyp eq=EQUALS tm=term
      { focus_opt, (mk_pattern (PatAscribed(pat, ascr)) (rr2 $loc(focus_opt) $loc(eq)), tm) }
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

layeredEffectDefinition:
  | LBRACE lid=uident bs=binders WITH r=tmNoEq RBRACE
    {
      let typ =  (* bs -> Effect *)
        let first_b, last_b =
          match bs with
          | [] ->
             raise_error (Fatal_SyntaxError,
                          "Syntax error: unexpected empty binders list in the layered effect definition")
                         (range_of_id lid)
          | _ -> hd bs, last bs in
        let r = union_ranges first_b.brange last_b.brange in
        mk_term (Product (bs, mk_term (Name (lid_of_str "Effect")) r Type_level)) r Type_level in
      let rec decls (r:term) =
        match r.tm with
        | Paren r -> decls r
        | Record (None, flds) ->
           flds |> List.map (fun (lid, t) ->
                              mk_decl (Tycon (false,
                                              false,
                                              [TyconAbbrev (ident_of_lid lid, [], None, t)]))
                                      t.range [])
        | _ ->
           raise_error (Fatal_SyntaxError,
                        "Syntax error: layered effect combinators should be declared as a record")
                       r.range in
      DefineEffect (lid, [], typ, decls r) }

effectDecl:
  | lid=lident action_params=binders EQUALS t=simpleTerm
    { mk_decl (Tycon (false, false, [TyconAbbrev(lid, action_params, None, t)])) (rr $loc) [] }

subEffect:
  | src_eff=quident SQUIGGLY_RARROW tgt_eff=quident EQUALS lift=simpleTerm
      { { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift; braced=false } }
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
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift; braced=true }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp; braced=true }
          | _ ->
             raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', and possibly 'lift_wp'}") (rr $loc)
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise_error (Fatal_UnexpectedIdentifier, "Unexpected identifier; expected {'lift', 'lift_wp'}") (rr $loc)
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp); braced=true }
     }

polymonadic_bind:
  | LPAREN m_eff=quident COMMA n_eff=quident RPAREN PIPE_RIGHT p_eff=quident EQUALS bind=simpleTerm
      { (m_eff, n_eff, p_eff, bind) }

polymonadic_subcomp:
  | m_eff=quident SUBTYPE n_eff=quident EQUALS subcomp=simpleTerm
    { (m_eff, n_eff, subcomp) }


/******************************************************************************/
/*                        Qualifiers, tags, ...                               */
/******************************************************************************/

qualifier:
  | ASSUME        { Assumption }
  | INLINE        {
    raise_error (Fatal_InlineRenamedAsUnfold, "The 'inline' qualifier has been renamed to 'unfold'") (rr $loc)
   }
  | UNFOLDABLE    {
              raise_error (Fatal_UnfoldableDeprecated, "The 'unfoldable' qualifier is no longer denotable; it is the default qualifier so just omit it") (rr $loc)
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

  | NOEQUALITY    { Noeq }
  | UNOPTEQUALITY { Unopteq }
  | NEW           { New }
  | LOGIC         { log_issue (rr $loc) (Warning_logicqualifier,
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

%public
tuplePattern:
  | pats=separated_nonempty_list(COMMA, constructorPattern)
      { match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) (rr $loc) }

constructorPattern:
  | pat=constructorPattern COLON_COLON pats=constructorPattern
      { mk_pattern (consPat (rr $loc(pats)) pat pats) (rr $loc) }
  | uid=quident args=nonempty_list(atomicPattern)
      {
        let head_pat = mk_pattern (PatName uid) (rr $loc(uid)) in
        mk_pattern (PatApp (head_pat, args)) (rr $loc)
      }
  | pat=atomicPattern
      { pat }

atomicPattern:
  | LPAREN pat=tuplePattern COLON t=simpleArrow phi_opt=refineOpt RPAREN
      {
        let pos_t = rr2 $loc(pat) $loc(t) in
        let pos = rr $loc in
        mkRefinedPattern pat t true phi_opt pos_t pos
      }
  | LBRACK pats=separated_list(SEMICOLON, tuplePattern) RBRACK
      { mk_pattern (PatList pats) (rr2 $loc($1) $loc($3)) }
  | LBRACE record_pat=right_flexible_nonempty_list(SEMICOLON, fieldPattern) RBRACE
      { mk_pattern (PatRecord record_pat) (rr $loc) }
  | LENS_PAREN_LEFT pat0=constructorPattern COMMA pats=separated_nonempty_list(COMMA, constructorPattern) LENS_PAREN_RIGHT
      { mk_pattern (PatTuple(pat0::pats, true)) (rr $loc) }
  | LPAREN pat=tuplePattern RPAREN   { pat }
  | tv=tvar                   { mk_pattern (PatTvar (tv, None, [])) (rr $loc(tv)) }
  | LPAREN op=operator RPAREN
      { mk_pattern (PatOp op) (rr $loc) }
  | UNDERSCORE
      { mk_pattern (PatWild (None, [])) (rr $loc) }
  | HASH UNDERSCORE
      { mk_pattern (PatWild (Some Implicit, [])) (rr $loc) }
  | c=constant
      { mk_pattern (PatConst c) (rr $loc(c)) }
  | BACKTICK_PERC q=atomicTerm
      { mk_pattern (PatVQuote q) (rr $loc) }
  | qual_id=aqualifiedWithAttrs(lident)
    {
      let (aqual, attrs), lid = qual_id in
      mk_pattern (PatVar (lid, aqual, attrs)) (rr $loc(qual_id)) }
  | uid=quident
      { mk_pattern (PatName uid) (rr $loc(uid)) }

fieldPattern:
  | p = separated_pair(qlident, EQUALS, tuplePattern)
      { p }
  | lid=qlident
      { lid, mk_pattern (PatVar (ident_of_lid lid, None, [])) (rr $loc(lid)) }

  (* (x : t) is already covered by atomicPattern *)
  (* we do *NOT* allow _ in multibinder () since it creates reduce/reduce conflicts when*)
  (* preprocessing to ocamlyacc/fsyacc (which is expected since the macro are expanded) *)
patternOrMultibinder:
  | LBRACE_BAR id=lidentOrUnderscore COLON t=simpleArrow BAR_RBRACE
      { let r = rr $loc in
        let w = mk_pattern (PatVar (id, Some TypeClassArg, [])) r in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) r]
      }

  | LBRACE_BAR t=simpleArrow BAR_RBRACE
      { let r = rr $loc in
        let id = gen r in
        let w = mk_pattern (PatVar (id, Some TypeClassArg, [])) r in
        let asc = (t, None) in
        [mk_pattern (PatAscribed(w, asc)) r]
      }
  | pat=atomicPattern { [pat] }
  | LPAREN qual_id0=aqualifiedWithAttrs(lident) qual_ids=nonempty_list(aqualifiedWithAttrs(lident)) COLON t=simpleArrow r=refineOpt RPAREN
      {
        let pos = rr $loc in
        let t_pos = rr $loc(t) in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun ((aq, attrs), x) -> mkRefinedPattern (mk_pattern (PatVar (x, aq, attrs)) pos) t false r t_pos pos) qual_ids
      }

binder:
  | aqualifiedWithAttrs_lid=aqualifiedWithAttrs(lidentOrUnderscore)
     {
       let (q, attrs), lid = aqualifiedWithAttrs_lid in
       mk_binder_with_attrs (Variable lid) (rr $loc(aqualifiedWithAttrs_lid)) Type_level q attrs
     }

  | tv=tvar { mk_binder (TVariable tv) (rr $loc) Kind None  }
       (* small regression here : fun (=x : t) ... is not accepted anymore *)

multiBinder:
  | LBRACE_BAR id=lidentOrUnderscore COLON t=simpleArrow BAR_RBRACE
      { let r = rr $loc in
        [mk_binder (Annotated (id, t)) r Type_level (Some TypeClassArg)]
      }

  | LBRACE_BAR t=simpleArrow BAR_RBRACE
      { let r = rr $loc in
        let id = gen r in
        [mk_binder (Annotated (id, t)) r Type_level (Some TypeClassArg)]
      }

  | LPAREN qual_ids=nonempty_list(aqualifiedWithAttrs(lidentOrUnderscore)) COLON t=simpleArrow r=refineOpt RPAREN
     {
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun ((q, attrs), x) ->
         mkRefinedBinder x t should_bind_var r (rr $loc) q attrs) qual_ids
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

%public
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
  | op=MATCH_OP { Some (mk_ident ("let" ^ op, rr $loc(op))) }

ifMaybeOp:
  | IF {None}
  | op=IF_OP { Some (mk_ident ("let" ^ op, rr $loc(op))) }

%public
lidentOrUnderscore:
  | id=IDENT { mk_ident(id, rr $loc(id))}
  | UNDERSCORE { gen (rr $loc) }

%public
lident:
  | id=IDENT { mk_ident(id, rr $loc(id))}

uident:
  | id=NAME { mk_ident(id, rr $loc(id)) }

tvar:
  | tv=TVAR { mk_ident(tv, rr $loc(tv)) }


/******************************************************************************/
/*                            Types and terms                                 */
/******************************************************************************/

thunk(X): | t=X { mk_term (Abs ([mk_pattern (PatWild (None, [])) (rr $loc)], t)) (rr $loc) Expr }

thunk2(X):
  | t=X
     { let u = mk_term (Const Const_unit) (rr $loc) Expr in
       let t = mk_term (Seq (u, t)) (rr $loc) Expr in
       mk_term (Abs ([mk_pattern (PatWild (None, [])) (rr $loc)], t)) (rr $loc) Expr }

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
      { mk_term (Seq(e1, e2)) (rr2 $loc(e1) $loc(e2)) Expr }
(* Added this form for sequencing; *)
(* but it results in an additional shift/reduce conflict *)
(* ... which is actually be benign, since the same conflict already *)
(*     exists for the previous production *)
  | e1=noSeqTerm op=SEMICOLON_OP e2=term
      { let t = match op with
	  | Some op ->
	     let op = mk_ident ("let" ^ op, rr $loc(op)) in
	     let pat = mk_pattern (PatWild(None, [])) (rr $loc(op)) in
	     LetOperator ([(op, pat, e1)], e2)
	  | None   ->
             log_issue (rr $loc) (Warning_DeprecatedLightDoNotation, do_notation_deprecation_warning);
	     Bind(gen (rr $loc(op)), e1, e2)
        in mk_term t (rr2 $loc(e1) $loc(e2)) Expr
      }
  | x=lidentOrUnderscore LONG_LEFT_ARROW e1=noSeqTerm SEMICOLON e2=term
    { log_issue (rr $loc) (Warning_DeprecatedLightDoNotation, do_notation_deprecation_warning);
      mk_term (Bind(x, e1, e2)) (rr2 $loc(x) $loc(e2)) Expr }

match_returning:
  | as_opt=option(AS i=lident {i}) RETURNS t=tmIff {as_opt,t,false}
  | as_opt=option(AS i=lident {i}) RETURNS_EQ t=tmIff {as_opt,t,true}

%public
noSeqTerm:
  | t=typ  { t }
  | e=tmIff SUBTYPE t=tmIff tactic_opt=option(BY tactic=thunk(typ) {tactic})
      { mk_term (Ascribed(e,{t with level=Expr},tactic_opt,false)) (rr2 $loc(e) $loc(tactic_opt)) Expr }
  | e=tmIff EQUALTYPE t=tmIff tactic_opt=option(BY tactic=thunk(typ) {tactic})
      {
        log_issue (rr $loc)
	          (Warning_BleedingEdge_Feature,
		   "Equality type ascriptions is an experimental feature subject to redesign in the future");
        mk_term (Ascribed(e,{t with level=Expr},tactic_opt,true)) (rr2 $loc(e) $loc(tactic_opt)) Expr
      }
  | e1=atomicTermNotQUident op_expr=dotOperator LARROW e3=noSeqTerm
      {
        let (op, e2, _) = op_expr in
        let opid = mk_ident (string_of_id op ^ "<-", range_of_id op) in
        mk_term (Op(opid, [ e1; e2; e3 ])) (rr2 $loc(e1) $loc(e3)) Expr
      }
  | REQUIRES t=typ
      { mk_term (Requires(t, None)) (rr2 $loc($1) $loc(t)) Type_level }
  | ENSURES t=typ
      { mk_term (Ensures(t, None)) (rr2 $loc($1) $loc(t)) Type_level }
  | DECREASES t=typ
      { mk_term (Decreases (t, None)) (rr2 $loc($1) $loc(t)) Type_level }
  | DECREASES LBRACE_COLON_WELL_FOUNDED t=noSeqTerm RBRACE
      (*
       * decreases clause with relation is written as e1 e2,
       *   where e1 is a relation and e2 is a term
       *
       * this is parsed as an app node, so we destruct the app node
       *)
      { match t.tm with
        | App (t1, t2, _) ->
	  let ot = mk_term (WFOrder (t1, t2)) (rr2 $loc(t) $loc(t)) Type_level in
	  mk_term (Decreases (ot, None)) (rr2 $loc($1) $loc($4)) Type_level
	| _ ->
	  raise_error (Fatal_SyntaxError,
	    "Syntax error: To use well-founded relations, write e1 e2") (rr $loc(t)) }

  | ATTRIBUTES es=nonempty_list(atomicTerm)
      { mk_term (Attributes es) (rr2 $loc($1) $loc(es)) Type_level }
  | op=ifMaybeOp e1=noSeqTerm ret_opt=option(match_returning) THEN e2=noSeqTerm ELSE e3=noSeqTerm
      { mk_term (If(e1, op, ret_opt, e2, e3)) (rr2 $loc(op) $loc(e3)) Expr }
  | op=ifMaybeOp e1=noSeqTerm ret_opt=option(match_returning) THEN e2=noSeqTerm
      {
        let e3 = mk_term (Const Const_unit) (rr2 $loc(op) $loc(e2)) Expr in
        mk_term (If(e1, op, ret_opt, e2, e3)) (rr2 $loc(op) $loc(e2)) Expr
      }
  | TRY e1=term WITH pbs=left_flexible_nonempty_list(BAR, patternBranch)
      {
         let branches = focusBranches (pbs) (rr2 $loc($1) $loc(pbs)) in
         mk_term (TryWith(e1, branches)) (rr2 $loc($1) $loc(pbs)) Expr
      }
  | op=matchMaybeOp e=term ret_opt=option(match_returning) WITH pbs=left_flexible_list(BAR, pb=patternBranch {pb})
      {
        let branches = focusBranches pbs (rr2 $loc(op) $loc(pbs)) in
        mk_term (Match(e, op, ret_opt, branches)) (rr2 $loc(op) $loc(pbs)) Expr
      }
  | LET OPEN t=term IN e=term
      {
            match t.tm with
            | Ascribed(r, rty, None, _) ->
              mk_term (LetOpenRecord(r, rty, e)) (rr2 $loc($1) $loc(e)) Expr

            | Name uid ->
              mk_term (LetOpen(uid, e)) (rr2 $loc($1) $loc(e)) Expr

            | _ ->
              raise_error (Fatal_SyntaxError, "Syntax error: local opens expects either opening\n\
                                               a module or namespace using `let open T in e`\n\
                                               or, a record type with `let open e <: t in e'`")
                          (rr $loc(t))
      }

  | attrs=ioption(attribute)
    LET q=letqualifier lb=letbinding lbs=list(attr_letbinding) IN e=term
      {
        let lbs = (attrs, lb)::lbs in
        let lbs = focusAttrLetBindings lbs (rr2 $loc(q) $loc(lb)) in
        mk_term (Let(q, lbs, e)) (rr $loc) Expr
      }
  | op=let_op b=letoperatorbinding lbs=list(op=and_op b=letoperatorbinding {(op, b)}) IN e=term
    { let lbs = (op, b)::lbs in
      mk_term (LetOperator ( List.map (fun (op, (pat, tm)) -> (op, pat, tm)) lbs
			   , e)) (rr2 $loc(op) $loc(e)) Expr
    }
  | FUNCTION pbs=left_flexible_nonempty_list(BAR, patternBranch)
      {
        let branches = focusBranches pbs (rr2 $loc($1) $loc(pbs)) in
        mk_function branches (rr $loc) (rr2 $loc($1) $loc(pbs))
      }
  | a=ASSUME e=atomicTerm
      { let a = set_lid_range assume_lid (rr $loc(a)) in
        mkExplicitApp (mk_term (Var a) (rr $loc(a)) Expr) [e] (rr $loc)
      }

  | a=ASSERT e=atomicTerm tactic_opt=option(BY tactic=thunk2(typ) {tactic})
      {
        match tactic_opt with
        | None ->
          let a = set_lid_range assert_lid (rr $loc(a)) in
          mkExplicitApp (mk_term (Var a) (rr $loc(a)) Expr) [e] (rr $loc)
        | Some tac ->
          let a = set_lid_range assert_by_tactic_lid (rr $loc(a)) in
          mkExplicitApp (mk_term (Var a) (rr $loc(a)) Expr) [e; tac] (rr $loc)
      }

   | u=UNDERSCORE BY tactic=thunk(atomicTerm)
     {
         let a = set_lid_range synth_lid (rr $loc(u)) in
         mkExplicitApp (mk_term (Var a) (rr $loc(u)) Expr) [tactic] (rr $loc)
     }

   | s=SYNTH tactic=atomicTerm
     {
         let a = set_lid_range synth_lid (rr $loc(s)) in
         mkExplicitApp (mk_term (Var a) (rr $loc(s)) Expr) [tactic] (rr $loc)
     }

   | CALC rel=atomicTerm LBRACE init=noSeqTerm SEMICOLON steps=list(calcStep) RBRACE
     {
         mk_term (CalcProof (rel, init, steps)) (rr2 $loc($1) $loc($7)) Expr
     }

   | INTRO FORALL bs=binders DOT p=noSeqTerm WITH e=noSeqTerm
     {
        mk_term (IntroForall(bs, p, e)) (rr2 $loc($1) $loc(e)) Expr
     }

   | INTRO EXISTS bs=binders DOT p=noSeqTerm WITH vs=list(atomicTerm) AND e=noSeqTerm
     {
        if List.length bs <> List.length vs
        then raise_error (Fatal_SyntaxError, "Syntax error: expected instantiations for all binders") (rr $loc(vs))
        else mk_term (IntroExists(bs, p, vs, e)) (rr2 $loc($1) $loc(e)) Expr
     }

   | INTRO p=tmFormula IMPLIES q=tmFormula WITH y=singleBinder DOT e=noSeqTerm
     {
        mk_term (IntroImplies(p, q, y, e)) (rr2 $loc($1) $loc(e)) Expr
     }

   | INTRO p=tmFormula DISJUNCTION q=tmConjunction WITH lr=NAME e=noSeqTerm
     {
        let b =
            if lr = "Left" then true
            else if lr = "Right" then false
            else raise_error (Fatal_SyntaxError, "Syntax error: _intro_ \\/ expects either 'Left' or 'Right'") (rr $loc(lr))
        in
        mk_term (IntroOr(b, p, q, e))  (rr2 $loc($1) $loc(e)) Expr
     }

   | INTRO p=tmConjunction CONJUNCTION q=tmTuple WITH e1=noSeqTerm AND e2=noSeqTerm
     {
        mk_term (IntroAnd(p, q, e1, e2))  (rr2 $loc($1) $loc(e2)) Expr
     }

   | ELIM FORALL xs=binders DOT p=noSeqTerm WITH vs=list(atomicTerm)
     {
        mk_term (ElimForall(xs, p, vs)) (rr2 $loc($1) $loc(vs)) Expr
     }

   | ELIM EXISTS bs=binders DOT p=noSeqTerm RETURNS q=noSeqTerm WITH y=singleBinder DOT e=noSeqTerm
     {
        mk_term (ElimExists(bs, p, q, y, e)) (rr2 $loc($1) $loc(e)) Expr
     }

   | ELIM p=tmFormula IMPLIES q=tmFormula WITH e=noSeqTerm
     {
        mk_term (ElimImplies(p, q, e)) (rr2 $loc($1) $loc(e)) Expr
     }

   | ELIM p=tmFormula DISJUNCTION q=tmConjunction RETURNS r=noSeqTerm WITH x=singleBinder DOT e1=noSeqTerm AND y=singleBinder DOT e2=noSeqTerm
     {
        mk_term (ElimOr(p, q, r, x, e1, y, e2)) (rr2 $loc($1) $loc(e2)) Expr
     }

   | ELIM p=tmConjunction CONJUNCTION q=tmTuple RETURNS r=noSeqTerm WITH xs=binders DOT e=noSeqTerm
     {
        match xs with
        | [x;y] -> mk_term (ElimAnd(p, q, r, x, y, e)) (rr2 $loc($1) $loc(e)) Expr
     }

singleBinder:
  | bs=binders
    {
       match bs with
       | [b] -> b
       | _ -> raise_error (Fatal_SyntaxError, "Syntax error: expected a single binder") (rr $loc(bs))
    }

calcRel:
  | i=binop_name { mk_term (Op (i, [])) (rr $loc(i)) Expr }
  | BACKTICK id=qlident BACKTICK { mk_term (Var id) (rr $loc) Un }
  | t=atomicTerm { t }

calcStep:
   | rel=calcRel LBRACE justif=option(term) RBRACE next=noSeqTerm SEMICOLON
     {
         let justif =
             match justif with
             | Some t -> t
             | None -> mk_term (Const Const_unit) (rr2 $loc($2) $loc($4)) Expr
         in
         CalcStep (rel, justif, next)
     }

typ:
  | t=simpleTerm { t }

  | q=quantifier bs=binders DOT trigger=trigger e=noSeqTerm
      {
        match bs with
        | [] ->
          raise_error (Fatal_MissingQuantifierBinder, "Missing binders for a quantifier") (rr2 $loc(q) $loc($3))
        | _ ->
          let idents = idents_of_binders bs (rr2 $loc(q) $loc($3)) in
          mk_term (q (bs, (idents, trigger), e)) (rr2 $loc(q) $loc(e)) Formula
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
      { mk_term (Abs(flatten pats, e)) (rr2 $loc($1) $loc(e)) Un }

maybeFocusArrow:
  | RARROW          { false }
  | SQUIGGLY_RARROW { true }

patternBranch:
  | pat=disjunctivePattern when_opt=maybeWhen focus=maybeFocusArrow e=term
      {
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rr2 $loc(pat) $loc(pat))
        in
        (focus, (pat, when_opt, e))
      }

%inline maybeWhen:
  |                      { None }
  | WHEN e=tmFormula     { Some e }



tmIff:
  | e1=tmImplies tok=IFF e2=tmIff
      { mk_term (Op(mk_ident("<==>", rr $loc(tok)), [e1; e2])) (rr2 $loc(e1) $loc(e2)) Formula }
  | e=tmImplies { e }

tmImplies:
  | e1=tmArrow(tmFormula) tok=IMPLIES e2=tmImplies
      { mk_term (Op(mk_ident("==>", rr $loc(tok)), [e1; e2])) (rr2 $loc(e1) $loc(e2)) Formula }
  | e=tmArrow(tmFormula)
      { e }


(* Tm : either tmFormula, containing EQUALS or tmNoEq, without EQUALS *)
tmArrow(Tm):
  | dom=tmArrowDomain(Tm) RARROW tgt=tmArrow(Tm)
     {
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rr $loc(dom)) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rr2 $loc(dom) $loc(dom)) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rr2 $loc(dom) $loc(tgt))  Un
     }
  | e=Tm { e }

simpleArrow:
  | dom=simpleArrowDomain RARROW tgt=simpleArrow
     {
       let ((aq_opt, attrs), dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder_with_attrs (NoName dom_tm) (rr $loc(dom)) Un aq_opt attrs
         | Some (x, t, f) -> mkRefinedBinder x t true f (rr2 $loc(dom) $loc(dom)) aq_opt attrs
       in
       mk_term (Product([b], tgt)) (rr2 $loc(dom) $loc(tgt))  Un
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
  | e1=tmFormula tok=DISJUNCTION e2=tmConjunction
      { mk_term (Op(mk_ident("\\/", rr $loc(tok)), [e1;e2])) (rr2 $loc(e1) $loc(e2)) Formula }
  | e=tmConjunction { e }

tmConjunction:
  | e1=tmConjunction tok=CONJUNCTION e2=tmTuple
      { mk_term (Op(mk_ident("/\\", rr $loc(tok)), [e1;e2])) (rr2 $loc(e1) $loc(e2)) Formula }
  | e=tmTuple { e }

tmTuple:
  | el=separated_nonempty_list(COMMA, tmEq)
      {
        match el with
          | [x] -> x
          | components -> mkTuple components (rr2 $loc(el) $loc(el))
      }


tmEqWith(X):
  | e1=tmEqWith(X) tok=EQUALS e2=tmEqWith(X)
      { mk_term (Op(mk_ident("=", rr $loc(tok)), [e1; e2])) (rr $loc) Un}
  (* non-associativity of COLON_EQUALS is currently not well handled by fsyacc which reports a s/r conflict *)
  (* see https:/ /github.com/fsprojects/FsLexYacc/issues/39 *)
  | e1=tmEqWith(X) tok=COLON_EQUALS e2=tmEqWith(X)
      { mk_term (Op(mk_ident(":=", rr $loc(tok)), [e1; e2])) (rr $loc) Un}
  | e1=tmEqWith(X) tok=PIPE_RIGHT e2=tmEqWith(X)
      { mk_term (Op(mk_ident("|>", rr $loc(tok)), [e1; e2])) (rr $loc) Un}
  | e1=tmEqWith(X) op=operatorInfix0ad12 e2=tmEqWith(X)
      { mk_term (Op(op, [e1; e2])) (rr2 $loc(e1) $loc(e2)) Un}
  | e1=tmEqWith(X) tok=MINUS e2=tmEqWith(X)
      { mk_term (Op(mk_ident("-", rr $loc(tok)), [e1; e2])) (rr $loc) Un}
  | tok=MINUS e=tmEqWith(X)
      { mk_uminus e (rr $loc(tok)) (rr $loc) Expr }
  | QUOTE e=tmEqWith(X)
      { mk_term (Quote (e, Dynamic)) (rr $loc) Un }
  | BACKTICK e=tmEqWith(X)
      { mk_term (Quote (e, Static)) (rr $loc) Un }
  | BACKTICK_AT e=atomicTerm
      { let q = mk_term (Quote (e, Dynamic)) (rr $loc) Un in
        mk_term (Antiquote q) (rr $loc) Un }
  | BACKTICK_HASH e=atomicTerm
      { mk_term (Antiquote e) (rr $loc) Un }
  | e=tmNoEqWith(X)
      { e }

tmNoEqWith(X):
  | e1=tmNoEqWith(X) COLON_COLON e2=tmNoEqWith(X)
      { consTerm (rr $loc) e1 e2 }
  | e1=tmNoEqWith(X) AMP e2=tmNoEqWith(X)
      {
            let dom =
               match extract_named_refinement e1 with
               | Some (x, t, f) ->
                 let dom = mkRefinedBinder x t true f (rr $loc(e1)) None [] in
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
            mk_term (Sum(dom, res)) (rr2 $loc(e1) $loc(e2)) Type_level
      }
  | e1=tmNoEqWith(X) op=OPINFIX3 e2=tmNoEqWith(X)
      { mk_term (Op(mk_ident(op, rr $loc(op)), [e1; e2])) (rr $loc) Un}
  | e1=tmNoEqWith(X) BACKTICK op=tmNoEqWith(X) BACKTICK e2=tmNoEqWith(X)
      { mkApp op [ e1, Infix; e2, Nothing ] (rr $loc) }
 | e1=tmNoEqWith(X) op=OPINFIX4 e2=tmNoEqWith(X)
      { mk_term (Op(mk_ident(op, rr $loc(op)), [e1; e2])) (rr $loc) Un}
  | LBRACE e=recordExp RBRACE { e }
  | BACKTICK_PERC e=atomicTerm
      { mk_term (VQuote e) (rr $loc) Un }
  | op=TILDE e=atomicTerm
      { mk_term (Op(mk_ident (op, rr $loc(op)), [e])) (rr $loc) Formula }
  | e=X { e }

binop_name:
  | o=OPINFIX0a              { mk_ident (o, rr $loc) }
  | o=OPINFIX0b              { mk_ident (o, rr $loc) }
  | o=OPINFIX0c              { mk_ident (o, rr $loc) }
  | o=EQUALS                 { mk_ident ("=", rr $loc) }
  | o=OPINFIX0d              { mk_ident (o, rr $loc) }
  | o=OPINFIX1               { mk_ident (o, rr $loc) }
  | o=OPINFIX2               { mk_ident (o, rr $loc) }
  | o=OPINFIX3               { mk_ident (o, rr $loc) }
  | o=OPINFIX4               { mk_ident (o, rr $loc) }
  | o=IMPLIES                { mk_ident ("==>", rr $loc) }
  | o=CONJUNCTION            { mk_ident ("/\\", rr $loc) }
  | o=DISJUNCTION            { mk_ident ("\\/", rr $loc) }
  | o=IFF                    { mk_ident ("<==>", rr $loc) }
  | o=PIPE_RIGHT             { mk_ident ("|>", rr $loc) }
  | o=COLON_EQUALS           { mk_ident (":=", rr $loc) }
  | o=COLON_COLON            { mk_ident ("::", rr $loc) }
  | o=OP_MIXFIX_ASSIGNMENT   { mk_ident (o, rr $loc) }
  | o=OP_MIXFIX_ACCESS       { mk_ident (o, rr $loc) }

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
          | Some phi -> Refine(mk_binder (Annotated(id, e)) (rr2 $loc(id) $loc(e)) Type_level None, phi)
        in mk_term t (rr2 $loc(id) $loc(phi_opt)) Type_level
      }
  | e=appTerm  { e }

refineOpt:
  | phi_opt=option(LBRACE phi=formula RBRACE {phi}) {phi_opt}

%inline formula:
  | e=noSeqTerm { {e with level=Formula} }

recordExp:
  | record_fields=right_flexible_nonempty_list(SEMICOLON, simpleDef)
      { mk_term (Record (None, record_fields)) (rr $loc(record_fields)) Expr }
  | e=appTerm WITH  record_fields=right_flexible_nonempty_list(SEMICOLON, simpleDef)
      { mk_term (Record (Some e, record_fields)) (rr2 $loc(e) $loc(record_fields)) Expr }

simpleDef:
  | e=separated_pair(qlidentOrOperator, EQUALS, noSeqTerm) { e }
  | lid=qlidentOrOperator { lid, mk_term (Name (lid_of_ids [ ident_of_lid lid ])) (rr $loc(lid)) Un }

%inline appTermCommon(argTerm):
  | head=indexingTerm args=list(argTerm)
      { mkApp head (map (fun (x,y) -> (y,x)) args) (rr2 $loc(head) $loc(args)) }

%public
appTerm:
  | t=appTermCommon(t=argTerm {t} | h=maybeHash LBRACE t=recordExp RBRACE {h, t}) {t}

%public
appTermNoRecordExp:
  | t=appTermCommon(argTerm) {t}

argTerm:
  | x=pair(maybeHash, indexingTerm) { x }
  | u=universe { u }

%inline maybeHash:
  |      { Nothing }
  | HASH { Hash }

%public
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
        let e = mk_term t (rr $loc(id)) Un in
              e
    }
  | id=quident DOT_LPAREN t=term RPAREN
    {
      mk_term (LetOpen (id, t)) (rr2 $loc(id) $loc($4)) Expr
    }

atomicTermNotQUident:
  | UNDERSCORE { mk_term Wild (rr $loc) Un }
  | tv=tvar     { mk_term (Tvar tv) (rr $loc) Type_level }
  | c=constant { mk_term (Const c) (rr $loc) Expr }
  | x=opPrefixTerm(atomicTermNotQUident)
    { x }
  | LPAREN op=operator RPAREN
      { mk_term (Op(op, [])) (rr2 $loc($1) $loc($3)) Un }
  | LENS_PAREN_LEFT e0=tmEq COMMA el=separated_nonempty_list(COMMA, tmEq) LENS_PAREN_RIGHT
      { mkDTuple (e0::el) (rr2 $loc($1) $loc($5)) }
  | e=projectionLHS field_projs=list(DOT id=qlident {id})
      { fold_left (fun e lid -> mk_term (Project(e, lid)) (rr2 $loc(e) $loc(field_projs)) Expr ) e field_projs }
  | BEGIN e=term END
      { e }

(* Tm: atomicTermQUident or atomicTermNotQUident *)
opPrefixTerm(Tm):
  | op=OPPREFIX e=Tm
      { mk_term (Op(mk_ident(op, rr $loc(op)), [e])) (rr2 $loc(op) $loc(e)) Expr }


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
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level},None,false)) (rr2 $loc($1) $loc($4)) level
        in mk_term (Paren e1) (rr2 $loc($1) $loc($4)) (e.level)
      }
  | LBRACK_BAR es=semiColonTermList BAR_RBRACK
      {
        let l = mkConsList (rr2 $loc($1) $loc($3)) es in
        let pos = (rr2 $loc($1) $loc($3)) in
        mkExplicitApp (mk_term (Var (array_of_list_lid)) pos Expr) [l] pos
      }
  | LBRACK es=semiColonTermList RBRACK
      { mkConsList (rr2 $loc($1) $loc($3)) es }
  | PERCENT_LBRACK es=semiColonTermList RBRACK
      { mk_term (LexList es) (rr2 $loc($1) $loc($3)) Type_level }
  | BANG_LBRACE es=separated_list(COMMA, appTerm) RBRACE
      { mkRefSet (rr2 $loc($1) $loc($3)) es }
  | ns=quident QMARK_DOT id=lident
      { mk_term (Projector (ns, id)) (rr2 $loc(ns) $loc(id)) Expr }
  | lid=quident QMARK
      { mk_term (Discrim lid) (rr2 $loc(lid) $loc($2)) Un }

fsTypeArgs:
  | TYP_APP_LESS targs=separated_nonempty_list(COMMA, atomicTerm) TYP_APP_GREATER
    {targs}

(* Qid : quident or qlident.
   TypeArgs : option(fsTypeArgs) or someFsTypeArgs. *)
qidentWithTypeArgs(Qid,TypeArgs):
  | id=Qid targs_opt=TypeArgs
      {
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rr $loc(id)) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rr2 $loc(id) $loc(targs_opt))
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
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        Const_int (fst n, None)
     }
  | c=CHAR { Const_char c }
  | s=STRING { Const_string (s, rr $loc) }
  | TRUE { Const_bool true }
  | FALSE { Const_bool false }
  | r=REAL { Const_real r }
  | n=UINT8 { Const_int (n, Some (Unsigned, Int8)) }
  | n=INT8
      {
        if snd n then
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for 8-bit signed integers");
        Const_int (fst n, Some (Signed, Int8))
      }
  | n=UINT16 { Const_int (n, Some (Unsigned, Int16)) }
  | n=INT16
      {
        if snd n then
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for 16-bit signed integers");
        Const_int (fst n, Some (Signed, Int16))
      }
  | n=UINT32 { Const_int (n, Some (Unsigned, Int32)) }
  | n=INT32
      {
        if snd n then
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for 32-bit signed integers");
        Const_int (fst n, Some (Signed, Int32))
      }
  | n=UINT64 { Const_int (n, Some (Unsigned, Int64)) }
  | n=INT64
      {
        if snd n then
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for 64-bit signed integers");
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
         then log_issue (rr $loc(u1)) (Error_OpPlusInUniverse, ("The operator " ^ op_plus ^ " was found in universe context."
                           ^ "The only allowed operator in that context is +."));
         mk_term (Op(mk_ident (op_plus, rr $loc(op_plus)), [u1 ; u2])) (rr2 $loc(u1) $loc(u2)) Expr
       }
  | max=ident us=nonempty_list(atomicUniverse)
      {
        if string_of_id max <> string_of_lid max_lid
        then log_issue (rr $loc(max)) (Error_InvalidUniverseVar, "A lower case ident " ^ string_of_id max ^
                          " was found in a universe context. " ^
                          "It should be either max or a universe variable 'usomething.");
        let max = mk_term (Var (lid_of_ids [max])) (rr $loc(max)) Expr in
        mkApp max (map (fun u -> u, Nothing) us) (rr $loc)
      }

atomicUniverse:
  | UNDERSCORE
      { mk_term Wild (rr $loc) Expr }
  | n=INT
      {
        if snd n then
          log_issue (rr $loc) (Error_OutOfRange, "This number is outside the allowable range for representable integer constants");
        mk_term (Const (Const_int (fst n, None))) (rr $loc(n)) Expr
      }
  | u=lident { mk_term (Uvar u) (range_of_id u) Expr }
  | LPAREN u=universeFrom RPAREN
    { u (*mk_term (Paren u) (rr2 $loc($1) $loc($3)) Expr*) }

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

string:
  | s=STRING { s }

%inline operator:
  | op=OPPREFIX     { mk_ident (op, rr $loc) }
  | op=binop_name   { op }
  | op=TILDE        { mk_ident (op, rr $loc) }
  | op=and_op       {op}
  | op=let_op       {op}

%inline and_op:
  | op=AND_OP { mk_ident ("and" ^ op, rr $loc) }
%inline let_op:
  | op=LET_OP { mk_ident ("let" ^ op, rr $loc) }

/* These infix operators have a lower precedence than EQUALS */
%inline operatorInfix0ad12:
  | op=OPINFIX0a
  | op=OPINFIX0b
  | op=OPINFIX0c
  | op=OPINFIX0d
  | op=OPINFIX1
  | op=OPINFIX2
     { mk_ident (op, rr $loc) }

%inline dotOperator:
  | op=DOT_LPAREN e=term RPAREN { mk_ident (".()", rr $loc(op)), e, rr2 $loc(op) $loc($3) }
  | op=DOT_LBRACK e=term RBRACK { mk_ident (".[]", rr $loc(op)), e, rr2 $loc(op) $loc($3) }
  | op=DOT_LBRACK_BAR e=term BAR_RBRACK { mk_ident (".[||]", rr $loc(op)), e, rr2 $loc(op) $loc($3) }
  | op=DOT_LENS_PAREN_LEFT e=term LENS_PAREN_RIGHT { mk_ident (".(||)", rr $loc(op)), e, rr2 $loc(op) $loc($3) }

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

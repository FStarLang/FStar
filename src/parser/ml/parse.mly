%{
(*
 We are expected to have only 7 shift-reduce conflicts.
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
open FStar_Syntax_Const
open FStar_Syntax_Util
open FStar_Parser_AST
open FStar_Parser_Util
open FStar_Const
open FStar_Ident
open FStar_String
%}
%start inputFragment
%start term
%token ABSTRACT
%token AMP
%token AND
%token ASSERT
%token ASSUME
%token ATTRIBUTES
%token BACKTICK
%token BANG_LBRACE
%token BAR
%token BAR_RBRACK
%token BEGIN
%token BY
%token <bytes> BYTEARRAY
%token <char> CHAR
%token COLON
%token COLON_COLON
%token COLON_EQUALS
%token COMMA
%token CONJUNCTION
%token DEFAULT
%token DISJUNCTION
%token DOLLAR
%token DOT
%token DOT_LBRACK
%token DOT_LPAREN
%token EFFECT
%token ELSE
%token END
%token ENSURES
%token EOF
%token EQUALS
%token EXCEPTION
%token EXISTS
%token FALSE
%token FORALL
%token <FStar_Parser_AST.fsdoc> FSDOC
%token <FStar_Parser_AST.fsdoc> FSDOC_STANDALONE
%token FUN
%token FUNCTION
%token HASH
%token <string> IDENT
%token <float> IEEE64
%token IF
%token IFF
%token IMPLIES
%token IN
%token INCLUDE
%token INLINE
%token INLINE_FOR_EXTRACTION
%token <string * bool> INT
%token <string * bool> INT16
%token <string * bool> INT32
%token <string * bool> INT64
%token <string * bool> INT8
%token IRREDUCIBLE
%token LARROW
%token LBRACE
%token LBRACE_COLON_PATTERN
%token LBRACK
%token LBRACK_AT
%token LBRACK_BAR
%token LENS_PAREN_LEFT
%token LENS_PAREN_RIGHT
%token <bool> LET
%token LOGIC
%token LONG_LEFT_ARROW
%token LPAREN
%token LPAREN_RPAREN
%token L_FALSE
%token L_TRUE
%token MATCH
%token MINUS
%token MODULE
%token MUTABLE
%token <string> NAME
%token NEW
%token NEW_EFFECT
%token NOEQUALITY
%token NOEXTRACT
%token OF
%token OPAQUE
%token OPEN
%token <string> OPINFIX0a
%token <string> OPINFIX0b
%token <string> OPINFIX0c
%token <string> OPINFIX0d
%token <string> OPINFIX1
%token <string> OPINFIX2
%token <string> OPINFIX3
%token <string> OPINFIX4
%token <string> OPPREFIX
%token PERCENT_LBRACK
%token PIPE_RIGHT
%token PRAGMALIGHT
%token PRAGMA_RESET_OPTIONS
%token PRAGMA_SET_OPTIONS
%token PRIVATE
%token QMARK
%token QMARK_DOT
%token RARROW
%token RBRACE
%token RBRACK
%token REC
%token REFLECTABLE
%token REIFIABLE
%token REIFY
%token REQUIRES
%token RPAREN
%token SEMICOLON
%token SEMICOLON_SEMICOLON
%token SQUIGGLY_RARROW
%token <bytes> STRING
%token SUBKIND
%token SUBTYPE
%token SUB_EFFECT
%token THEN
%token <string> TILDE
%token TOTAL
%token TRUE
%token TRY
%token <string> TVAR
%token TYPE
%token TYP_APP_GREATER
%token TYP_APP_LESS
%token <string> UINT16
%token <string> UINT32
%token <string> UINT64
%token <string> UINT8
%token UNDERSCORE
%token UNFOLD
%token UNFOLDABLE
%token UNIV_HASH
%token UNOPTEQUALITY
%token VAL
%token WHEN
%token WITH
%nonassoc THEN
%nonassoc ELSE
%right COLON_COLON
%right AMP
%nonassoc COLON_EQUALS
%left OPINFIX0a
%left OPINFIX0b
%left EQUALS OPINFIX0c
%left OPINFIX0d
%left PIPE_RIGHT
%right OPINFIX1
%left MINUS OPINFIX2
%left OPINFIX3
%left BACKTICK
%right OPINFIX4
%type <inputFragment> inputFragment
%type <FStar_Ident.ident> lident
%type <term> term
%%

option_FSDOC_:
  
    {    ( None )}
| FSDOC
    {let x = $1 in
    ( Some x )}

option___anonymous_1_:
  
    {    ( None )}
| OF typ
    {let (_10, t0) = ((), $2) in
let x =
  let t = t0 in
  let _1 = _10 in
                                                 (t)
in
    ( Some x )}

option___anonymous_2_:
  
    {    ( None )}
| OF typ
    {let (_10, t0) = ((), $2) in
let x =
  let t = t0 in
  let _1 = _10 in
                                                          (t)
in
    ( Some x )}

option___anonymous_5_:
  
    {    ( None )}
| BY typ
    {let (_10, tactic0) = ((), $2) in
let x =
  let tactic = tactic0 in
  let _1 = _10 in
                                                              (tactic)
in
    ( Some x )}

option___anonymous_7_:
  
    {    ( None )}
| LBRACE noSeqTerm RBRACE
    {let (_10, e00, _30) = ((), $2, ()) in
let x =
  let _3 = _30 in
  let e0 = e00 in
  let _1 = _10 in
  let phi =
    let e = e0 in
                    ( {e with level=Formula} )
  in
                                               (phi)
in
    ( Some x )}

option_ascribeKind_:
  
    {    ( None )}
| ascribeKind
    {let x = $1 in
    ( Some x )}

option_ascribeTyp_:
  
    {    ( None )}
| ascribeTyp
    {let x = $1 in
    ( Some x )}

option_fsTypeArgs_:
  
    {    ( None )}
| fsTypeArgs
    {let x = $1 in
    ( Some x )}

option_mainDecl_:
  
    {    ( None )}
| mainDecl
    {let x = $1 in
    ( Some x )}

option_pair_hasSort_simpleTerm__:
  
    {    ( None )}
| hasSort simpleTerm
    {let (x0, y0) = ($1, $2) in
let x =
  let y = y0 in
  let x = x0 in
      ( (x, y) )
in
    ( Some x )}

option_string_:
  
    {    ( None )}
| STRING
    {let s0 = $1 in
let x =
  let s = s0 in
               ( string_of_bytes s )
in
    ( Some x )}

boption_SQUIGGLY_RARROW_:
  
    {    ( false )}
| SQUIGGLY_RARROW
    {let _1 = () in
    ( true )}

boption___anonymous_0_:
  
    {    ( false )}
| PRAGMALIGHT STRING
    {let (_10, _20) = ((), $2) in
let _1 =
  let _2 = _20 in
  let _1 = _10 in
                                          ( )
in
    ( true )}

loption_separated_nonempty_list_COMMA_appTerm__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_appTerm_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_SEMICOLON_tuplePattern__:
  
    {    ( [] )}
| separated_nonempty_list_SEMICOLON_tuplePattern_
    {let x = $1 in
    ( x )}

list___anonymous_4_:
  
    {    ( [] )}
| binder list___anonymous_4_
    {let (b0, xs) = ($1, $2) in
let x =
  let b = b0 in
                             ([b])
in
    ( x :: xs )}
| multiBinder list___anonymous_4_
    {let (bs0, xs) = ($1, $2) in
let x =
  let bs = bs0 in
                                                    (bs)
in
    ( x :: xs )}

list___anonymous_8_:
  
    {    ( [] )}
| DOT qlident list___anonymous_8_
    {let (_10, id0, xs) = ((), $2, $3) in
let x =
  let id = id0 in
  let _1 = _10 in
                                                      (id)
in
    ( x :: xs )}

list_argTerm_:
  
    {    ( [] )}
| argTerm list_argTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_atomicTerm_:
  
    {    ( [] )}
| atomicTerm list_atomicTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_constructorDecl_:
  
    {    ( [] )}
| constructorDecl list_constructorDecl_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_decl_:
  
    {    ( [] )}
| decl list_decl_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_decoration_:
  
    {    ( [] )}
| decoration list_decoration_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_multiBinder_:
  
    {    ( [] )}
| multiBinder list_multiBinder_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_aqualified_lident__:
  aqualified_lident_
    {let x = $1 in
    ( [ x ] )}
| aqualified_lident_ nonempty_list_aqualified_lident__
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_aqualified_lidentOrUnderscore__:
  aqualified_lidentOrUnderscore_
    {let x = $1 in
    ( [ x ] )}
| aqualified_lidentOrUnderscore_ nonempty_list_aqualified_lidentOrUnderscore__
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicPattern_:
  atomicPattern
    {let x = $1 in
    ( [ x ] )}
| atomicPattern nonempty_list_atomicPattern_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicTerm_:
  atomicTerm
    {let x = $1 in
    ( [ x ] )}
| atomicTerm nonempty_list_atomicTerm_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_atomicUniverse_:
  atomicUniverse
    {let x = $1 in
    ( [ x ] )}
| atomicUniverse nonempty_list_atomicUniverse_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_dotOperator_:
  DOT_LPAREN term RPAREN
    {let (_10, e0, _30) = ((), $2, ()) in
let x =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 )
in
    ( [ x ] )}
| DOT_LBRACK term RBRACK
    {let (_10, e0, _30) = ((), $2, ()) in
let x =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 )
in
    ( [ x ] )}
| DOT_LPAREN term RPAREN nonempty_list_dotOperator_
    {let (_10, e0, _30, xs) = ((), $2, (), $4) in
let x =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 )
in
    ( x :: xs )}
| DOT_LBRACK term RBRACK nonempty_list_dotOperator_
    {let (_10, e0, _30, xs) = ((), $2, (), $4) in
let x =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 )
in
    ( x :: xs )}

nonempty_list_patternOrMultibinder_:
  patternOrMultibinder
    {let x = $1 in
    ( [ x ] )}
| patternOrMultibinder nonempty_list_patternOrMultibinder_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

separated_nonempty_list_AND_letbinding_:
  letbinding
    {let x = $1 in
    ( [ x ] )}
| letbinding AND separated_nonempty_list_AND_letbinding_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_AND_pair_option_FSDOC__typeDecl__:
  option_FSDOC_ typeDecl
    {let (x0, y0) = ($1, $2) in
let x =
  let y = y0 in
  let x = x0 in
      ( (x, y) )
in
    ( [ x ] )}
| option_FSDOC_ typeDecl AND separated_nonempty_list_AND_pair_option_FSDOC__typeDecl__
    {let (x0, y0, _2, xs) = ($1, $2, (), $4) in
let x =
  let y = y0 in
  let x = x0 in
      ( (x, y) )
in
    ( x :: xs )}

separated_nonempty_list_BAR_tuplePattern_:
  tuplePattern
    {let x = $1 in
    ( [ x ] )}
| tuplePattern BAR separated_nonempty_list_BAR_tuplePattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_appTerm_:
  appTerm
    {let x = $1 in
    ( [ x ] )}
| appTerm COMMA separated_nonempty_list_COMMA_appTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_atomicTerm_:
  atomicTerm
    {let x = $1 in
    ( [ x ] )}
| atomicTerm COMMA separated_nonempty_list_COMMA_atomicTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_constructorPattern_:
  constructorPattern
    {let x = $1 in
    ( [ x ] )}
| constructorPattern COMMA separated_nonempty_list_COMMA_constructorPattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_tmEq_:
  tmEq
    {let x = $1 in
    ( [ x ] )}
| tmEq COMMA separated_nonempty_list_COMMA_tmEq_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_tvar_:
  tvar
    {let x = $1 in
    ( [ x ] )}
| tvar COMMA separated_nonempty_list_COMMA_tvar_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_DISJUNCTION_conjunctivePat_:
  conjunctivePat
    {let x = $1 in
    ( [ x ] )}
| conjunctivePat DISJUNCTION separated_nonempty_list_DISJUNCTION_conjunctivePat_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_appTerm_:
  appTerm
    {let x = $1 in
    ( [ x ] )}
| appTerm SEMICOLON separated_nonempty_list_SEMICOLON_appTerm_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_effectDecl_:
  effectDecl
    {let x = $1 in
    ( [ x ] )}
| effectDecl SEMICOLON separated_nonempty_list_SEMICOLON_effectDecl_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_fieldPattern_:
  fieldPattern
    {let x = $1 in
    ( [ x ] )}
| fieldPattern SEMICOLON separated_nonempty_list_SEMICOLON_fieldPattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_tuplePattern_:
  tuplePattern
    {let x = $1 in
    ( [ x ] )}
| tuplePattern SEMICOLON separated_nonempty_list_SEMICOLON_tuplePattern_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

inputFragment:
  boption___anonymous_0_ list_decl_ option_mainDecl_ EOF
    {let (is_light, decls, main_opt, _4) = ($1, $2, $3, ()) in
      (
        let decls = match main_opt with
           | None -> decls
           | Some main -> decls @ [main]
        in as_frag is_light (rhs parseState 1) decls
      )}

mainDecl:
  SEMICOLON_SEMICOLON option_FSDOC_ term
    {let (_1, doc, t) = ((), $2, $3) in
      ( let decorations = match doc with
        | Some d -> [ Doc d ]
        | _ -> [] in
        mk_decl (Main t) (rhs2 parseState 1 3) decorations
      )}

pragma:
  PRAGMA_SET_OPTIONS STRING
    {let (_1, s0) = ((), $2) in
let s =
  let s = s0 in
               ( string_of_bytes s )
in
      ( SetOptions s )}
| PRAGMA_RESET_OPTIONS option_string_
    {let (_1, s_opt) = ((), $2) in
      ( ResetOptions s_opt )}

decoration:
  FSDOC
    {let x = $1 in
      ( Doc x )}
| LBRACK_AT list_atomicTerm_ RBRACK
    {let (_1, x, _3) = ((), $2, ()) in
      ( DeclAttributes x )}
| qualifier
    {let x = $1 in
      ( Qualifier x )}

decl:
  ASSUME uident COLON noSeqTerm
    {let (_1, lid, _3, e0) = ((), $2, (), $4) in
let phi =
  let e = e0 in
                  ( {e with level=Formula} )
in
      ( mk_decl (Assume(lid, phi)) (rhs2 parseState 1 4) [ Qualifier Assumption ] )}
| decoration list_decoration_ rawDecl
    {let (d, ds, decl) = ($1, $2, $3) in
      ( mk_decl decl (rhs parseState 3) (d :: ds) )}
| rawDecl
    {let decl = $1 in
      ( mk_decl decl (rhs parseState 1) [] )}

rawDecl:
  pragma
    {let p = $1 in
      ( Pragma p )}
| OPEN quident
    {let (_1, uid) = ((), $2) in
      ( Open uid )}
| INCLUDE quident
    {let (_1, uid) = ((), $2) in
      ( Include uid )}
| MODULE uident EQUALS quident
    {let (_1, uid1, _3, uid2) = ((), $2, (), $4) in
      ( ModuleAbbrev(uid1, uid2) )}
| MODULE quident
    {let (_1, uid) = ((), $2) in
      (  TopLevelModule uid )}
| TYPE separated_nonempty_list_AND_pair_option_FSDOC__typeDecl__
    {let (_1, tcdefs) = ((), $2) in
      ( Tycon (false, List.map (fun (doc, f) -> (f, doc)) tcdefs) )}
| EFFECT uident typars EQUALS typ
    {let (_1, uid, tparams, _4, t) = ((), $2, $3, (), $5) in
      ( Tycon(true, [(TyconAbbrev(uid, tparams, None, t), None)]) )}
| LET letqualifier separated_nonempty_list_AND_letbinding_
    {let (_1, q, lbs) = ($1, $2, $3) in
      (
        let r = rhs2 parseState 1 3 in
        let lbs = focusLetBindings lbs r in
        if q <> Rec && List.length lbs <> 1
        then raise (Error ("Unexpected multiple let-binding (Did you forget some rec qualifier ?)", r)) ;
        TopLevelLet(q, lbs)
      )}
| VAL lidentOrOperator list_multiBinder_ COLON typ
    {let (_1, lid, bss, _4, t) = ((), $2, $3, (), $5) in
      (
        let t = match flatten bss with
          | [] -> t
          | bs -> mk_term (Product(bs, t)) (rhs2 parseState 3 5) Type_level
        in Val(lid, t)
      )}
| EXCEPTION uident option___anonymous_1_
    {let (_1, lid, t_opt) = ((), $2, $3) in
      ( Exception(lid, t_opt) )}
| NEW_EFFECT newEffect
    {let (_1, ne) = ((), $2) in
      ( NewEffect ne )}
| SUB_EFFECT subEffect
    {let (_1, se) = ((), $2) in
      ( SubEffect se )}
| FSDOC_STANDALONE
    {let doc = $1 in
      ( Fsdoc doc )}

typeDecl:
  ident typars option_ascribeKind_ typeDefinition
    {let (lid, tparams, ascr_opt, tcdef) = ($1, $2, $3, $4) in
      ( tcdef lid tparams ascr_opt )}

typars:
  tvarinsts
    {let x = $1 in
                             ( x )}
| binders
    {let x = $1 in
                             ( x )}

tvarinsts:
  TYP_APP_LESS separated_nonempty_list_COMMA_tvar_ TYP_APP_GREATER
    {let (_1, tvs, _3) = ((), $2, ()) in
      ( map (fun tv -> mk_binder (TVariable(tv)) tv.idRange Kind None) tvs )}

typeDefinition:
  
    {      ( (fun id binders kopt -> check_id id; TyconAbstract(id, binders, kopt)) )}
| EQUALS typ
    {let (_1, t) = ((), $2) in
      ( (fun id binders kopt ->  check_id id; TyconAbbrev(id, binders, kopt, t)) )}
| EQUALS LBRACE right_flexible_nonempty_list_SEMICOLON_recordFieldDecl_ RBRACE
    {let (_1, _2, record_field_decls, _4) = ((), (), $3, ()) in
      ( (fun id binders kopt -> check_id id; TyconRecord(id, binders, kopt, record_field_decls)) )}
| EQUALS list_constructorDecl_
    {let (_1, ct_decls) = ((), $2) in
      ( (fun id binders kopt -> check_id id; TyconVariant(id, binders, kopt, ct_decls)) )}

recordFieldDecl:
  lident COLON typ
    {let (lid, _3, t) = ($1, (), $3) in
let doc_opt =
      ( None )
in
      ( (lid, t, doc_opt) )}
| FSDOC lident COLON typ
    {let (x0, lid, _3, t) = ($1, $2, (), $4) in
let doc_opt =
  let x = x0 in
      ( Some x )
in
      ( (lid, t, doc_opt) )}

constructorDecl:
  BAR option_FSDOC_ uident COLON typ
    {let (_1, doc_opt, uid, _4, t) = ((), $2, $3, (), $5) in
                                                             ( (uid, Some t, doc_opt, false) )}
| BAR option_FSDOC_ uident option___anonymous_2_
    {let (_1, doc_opt, uid, t_opt) = ((), $2, $3, $4) in
                                                             ( (uid, t_opt, doc_opt, true) )}

letbinding:
  maybeFocus lidentOrOperator nonempty_list_patternOrMultibinder_ option_ascribeTyp_ EQUALS term
    {let (focus_opt, lid, lbp, ascr_opt, _5, tm) = ($1, $2, $3, $4, (), $6) in
      (
        let pat = mk_pattern (PatVar(lid, None)) (rhs parseState 2) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rhs2 parseState 1 3) in
        let pos = rhs2 parseState 1 6 in
        match ascr_opt with
        | None -> (focus_opt, (pat, tm))
        | Some t -> (focus_opt, (mk_pattern (PatAscribed(pat, t)) pos, tm))
      )}
| maybeFocus tuplePattern ascribeTyp EQUALS term
    {let (focus_opt, pat, ascr, _4, tm) = ($1, $2, $3, (), $5) in
      ( focus_opt, (mk_pattern (PatAscribed(pat, ascr)) (rhs2 parseState 1 4), tm) )}
| maybeFocus tuplePattern EQUALS term
    {let (focus_opt, pat, _3, tm) = ($1, $2, (), $4) in
      ( focus_opt, (pat, tm) )}

newEffect:
  effectRedefinition
    {let ed = $1 in
    ( ed )}
| effectDefinition
    {let ed = $1 in
    ( ed )}

effectRedefinition:
  uident EQUALS simpleTerm
    {let (lid, _2, t) = ($1, (), $3) in
    ( RedefineEffect(lid, [], t) )}

effectDefinition:
  LBRACE uident binders COLON tmArrow_tmNoEq_ WITH separated_nonempty_list_SEMICOLON_effectDecl_ RBRACE
    {let (_1, lid, bs, _4, typ, _6, eds, _8) = ((), $2, $3, (), $5, (), $7, ()) in
    ( DefineEffect(lid, bs, typ, eds) )}

effectDecl:
  lident binders EQUALS simpleTerm
    {let (lid, action_params, _3, t) = ($1, $2, (), $4) in
    ( mk_decl (Tycon (false, [TyconAbbrev(lid, action_params, None, t), None])) (rhs2 parseState 1 3) [] )}

subEffect:
  quident SQUIGGLY_RARROW quident EQUALS simpleTerm
    {let (src_eff, _2, tgt_eff, _4, lift) = ($1, (), $3, (), $5) in
      ( { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift } )}
| quident SQUIGGLY_RARROW quident LBRACE IDENT EQUALS simpleTerm RBRACE
    {let (src_eff, _2, tgt_eff, _4, x0, _20, y0, _7) = ($1, (), $3, (), $5, (), $7, ()) in
let lift2_opt =
      ( None )
in
let lift1 =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
     (
       match lift2_opt with
       | None ->
          begin match lift1 with
          | ("lift", lift) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp }
          | _ ->
             raise (Error("Unexpected identifier; expected {'lift', and possibly 'lift_wp'}", lhs parseState))
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise (Error("Unexpected identifier; expected {'lift', 'lift_wp'}", lhs parseState))
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp) }
     )}
| quident SQUIGGLY_RARROW quident LBRACE IDENT EQUALS simpleTerm SEMICOLON IDENT EQUALS simpleTerm RBRACE
    {let (src_eff, _2, tgt_eff, _4, x0, _20, y0, _1000, id000, _200, y00, _7) = ($1, (), $3, (), $5, (), $7, (), $9, (), $11, ()) in
let lift2_opt =
  let y0 = y00 in
  let _20 = _200 in
  let id00 = id000 in
  let _100 = _1000 in
  let x =
    let y = y0 in
    let _2 = _20 in
    let id0 = id00 in
    let _10 = _100 in
    let x =
      let id = id0 in
      let _1 = _10 in
                                                                (id)
    in
        ( (x, y) )
  in
      ( Some x )
in
let lift1 =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
     (
       match lift2_opt with
       | None ->
          begin match lift1 with
          | ("lift", lift) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = LiftForFree lift }
          | ("lift_wp", lift_wp) ->
             { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift_wp }
          | _ ->
             raise (Error("Unexpected identifier; expected {'lift', and possibly 'lift_wp'}", lhs parseState))
          end
       | Some (id2, tm2) ->
          let (id1, tm1) = lift1 in
          let lift, lift_wp = match (id1, id2) with
                  | "lift_wp", "lift" -> tm1, tm2
                  | "lift", "lift_wp" -> tm2, tm1
                  | _ -> raise (Error("Unexpected identifier; expected {'lift', 'lift_wp'}", lhs parseState))
          in
          { msource = src_eff; mdest = tgt_eff; lift_op = ReifiableLift (lift, lift_wp) }
     )}

qualifier:
  ASSUME
    {let _1 = () in
                  ( Assumption )}
| INLINE
    {let _1 = () in
                  (
    raise (Error("The 'inline' qualifier has been renamed to 'unfold'", lhs parseState))
   )}
| UNFOLDABLE
    {let _1 = () in
                  (
              raise (Error("The 'unfoldable' qualifier is no longer denotable; it is the default qualifier so just omit it", lhs parseState))
   )}
| INLINE_FOR_EXTRACTION
    {let _1 = () in
                          (
     Inline_for_extraction
  )}
| UNFOLD
    {let _1 = () in
           (
     Unfold_for_unification_and_vcgen
  )}
| IRREDUCIBLE
    {let _1 = () in
                  ( Irreducible )}
| NOEXTRACT
    {let _1 = () in
                  ( NoExtract )}
| DEFAULT
    {let _1 = () in
                  ( DefaultEffect )}
| TOTAL
    {let _1 = () in
                  ( TotalEffect )}
| PRIVATE
    {let _1 = () in
                  ( Private )}
| ABSTRACT
    {let _1 = () in
                  ( Abstract )}
| NOEQUALITY
    {let _1 = () in
                  ( Noeq )}
| UNOPTEQUALITY
    {let _1 = () in
                  ( Unopteq )}
| NEW
    {let _1 = () in
                  ( New )}
| LOGIC
    {let _1 = () in
                  ( Logic )}
| OPAQUE
    {let _1 = () in
                  ( Opaque )}
| REIFIABLE
    {let _1 = () in
                  ( Reifiable )}
| REFLECTABLE
    {let _1 = () in
                  ( Reflectable )}

maybeFocus:
  boption_SQUIGGLY_RARROW_
    {let b = $1 in
                               ( b )}

letqualifier:
  REC
    {let _1 = () in
                ( Rec )}
| MUTABLE
    {let _1 = () in
                ( Mutable )}
| 
    {                ( NoLetQualifier )}

aqual:
  EQUALS
    {let _1 = () in
              ( print1 "%s (Warning): The '=' notation for equality constraints on binders is deprecated; use '$' instead\n" (string_of_range (lhs parseState));
                                        Equality )}
| aqualUniverses
    {let q = $1 in
                     ( q )}

aqualUniverses:
  HASH
    {let _1 = () in
              ( Implicit )}
| DOLLAR
    {let _1 = () in
              ( Equality )}

disjunctivePattern:
  separated_nonempty_list_BAR_tuplePattern_
    {let pats = $1 in
                                                    ( pats )}

tuplePattern:
  separated_nonempty_list_COMMA_constructorPattern_
    {let pats = $1 in
      ( match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) (rhs parseState 1) )}

constructorPattern:
  constructorPattern COLON_COLON constructorPattern
    {let (pat, _2, pats) = ($1, (), $3) in
      ( mk_pattern (consPat (rhs parseState 3) pat pats) (rhs2 parseState 1 3) )}
| quident nonempty_list_atomicPattern_
    {let (uid, args) = ($1, $2) in
      (
        let head_pat = mk_pattern (PatName uid) (rhs parseState 1) in
        mk_pattern (PatApp (head_pat, args)) (rhs2 parseState 1 2)
      )}
| atomicPattern
    {let pat = $1 in
      ( pat )}

atomicPattern:
  LPAREN tuplePattern COLON typ refineOpt RPAREN
    {let (_1, pat, _3, t, phi_opt, _6) = ((), $2, (), $4, $5, ()) in
      (
        let pos_t = rhs2 parseState 2 4 in
        let pos = rhs2 parseState 1 6 in
        mkRefinedPattern pat t true phi_opt pos_t pos
      )}
| LBRACK loption_separated_nonempty_list_SEMICOLON_tuplePattern__ RBRACK
    {let (_1, xs0, _3) = ((), $2, ()) in
let pats =
  let xs = xs0 in
      ( xs )
in
      ( mk_pattern (PatList pats) (rhs2 parseState 1 3) )}
| LBRACE separated_nonempty_list_SEMICOLON_fieldPattern_ RBRACE
    {let (_1, record_pat, _3) = ((), $2, ()) in
      ( mk_pattern (PatRecord record_pat) (rhs2 parseState 1 3) )}
| LENS_PAREN_LEFT constructorPattern COMMA separated_nonempty_list_COMMA_constructorPattern_ LENS_PAREN_RIGHT
    {let (_1, pat0, _3, pats, _5) = ((), $2, (), $4, ()) in
      ( mk_pattern (PatTuple(pat0::pats, true)) (rhs2 parseState 1 5) )}
| LPAREN tuplePattern RPAREN
    {let (_1, pat, _3) = ((), $2, ()) in
                                     ( pat )}
| tvar
    {let tv = $1 in
                              ( mk_pattern (PatTvar (tv, None)) (rhs parseState 1) )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX3 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX4 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX0a RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX0b RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX0c RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX0d RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX1 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX2 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN PIPE_RIGHT RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident("|>", rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN COLON_EQUALS RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident(":=", rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN COLON_COLON RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident("::", rhs parseState 1) )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| UNDERSCORE
    {let _1 = () in
      ( mk_pattern PatWild (rhs parseState 1) )}
| HASH UNDERSCORE
    {let (_1, _2) = ((), ()) in
      ( mk_pattern (PatVar (gen (rhs2 parseState 1 2), Some Implicit)) (rhs parseState 1) )}
| constant
    {let c = $1 in
      ( mk_pattern (PatConst c) (rhs parseState 1) )}
| aqualified_lident_
    {let qual_id = $1 in
      ( mk_pattern (PatVar (snd qual_id, fst qual_id)) (rhs parseState 1) )}
| quident
    {let uid = $1 in
      ( mk_pattern (PatName uid) (rhs parseState 1) )}

fieldPattern:
  qlident EQUALS tuplePattern
    {let (x0, _20, y0) = ($1, (), $3) in
let p =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
      ( p )}
| qlident
    {let lid = $1 in
      ( lid, mk_pattern (PatVar (lid.ident, None)) (rhs parseState 1) )}

patternOrMultibinder:
  atomicPattern
    {let pat = $1 in
                      ( [pat] )}
| LPAREN aqualified_lident_ nonempty_list_aqualified_lident__ COLON typ refineOpt RPAREN
    {let (_1, qual_id0, qual_ids, _4, t, r, _7) = ((), $2, $3, (), $5, $6, ()) in
      (
        let pos = rhs2 parseState 1 7 in
        let t_pos = rhs parseState 5 in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun (q, x) -> mkRefinedPattern (mk_pattern (PatVar (x, q)) pos) t false r t_pos pos) qual_ids
      )}

binder:
  aqualified_lidentOrUnderscore_
    {let aqualified_lid = $1 in
     (
       let (q, lid) = aqualified_lid in
       mk_binder (Variable lid) (rhs parseState 1) Type_level q
     )}
| tvar
    {let tv = $1 in
             ( mk_binder (TVariable tv) (rhs parseState 1) Kind None  )}

multiBinder:
  LPAREN nonempty_list_aqualified_lidentOrUnderscore__ COLON typ refineOpt RPAREN
    {let (_1, qual_ids, _3, t, r, _6) = ((), $2, (), $4, $5, ()) in
     (
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun (q, x) -> mkRefinedBinder x t should_bind_var r (rhs2 parseState 1 6) q) qual_ids
     )}

binders:
  list___anonymous_4_
    {let bss = $1 in
                                                        ( flatten bss )}

aqualified_lident_:
  lident
    {let y0 = $1 in
let x =
  let y = y0 in
  let x =
        ( None )
  in
      ( (x, y) )
in
                                                  ( x )}
| aqualUniverses lident
    {let (x00, y0) = ($1, $2) in
let x =
  let y = y0 in
  let x0 = x00 in
  let x =
    let x = x0 in
        ( Some x )
  in
      ( (x, y) )
in
                                                  ( x )}

aqualified_lidentOrUnderscore_:
  lidentOrUnderscore
    {let y0 = $1 in
let x =
  let y = y0 in
  let x =
        ( None )
  in
      ( (x, y) )
in
                                                  ( x )}
| aqualUniverses lidentOrUnderscore
    {let (x00, y0) = ($1, $2) in
let x =
  let y = y0 in
  let x0 = x00 in
  let x =
    let x = x0 in
        ( Some x )
  in
      ( (x, y) )
in
                                                  ( x )}

qlident:
  path_lident_
    {let ids = $1 in
                     ( lid_of_ids ids )}

quident:
  path_uident_
    {let ids = $1 in
                     ( lid_of_ids ids )}

path_lident_:
  lident
    {let id = $1 in
          ( [id] )}
| uident DOT path_lident_
    {let (uid, _2, p) = ($1, (), $3) in
                              ( uid::p )}

path_uident_:
  uident
    {let id = $1 in
          ( [id] )}
| uident DOT path_uident_
    {let (uid, _2, p) = ($1, (), $3) in
                              ( uid::p )}

ident:
  lident
    {let x = $1 in
             ( x )}
| uident
    {let x = $1 in
              ( x )}

lidentOrOperator:
  IDENT
    {let id = $1 in
    ( mk_ident(id, rhs parseState 1) )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let id =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX3 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let id =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX4 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let id =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX0a RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX0b RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX0c RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX0d RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX1 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN OPINFIX2 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let id =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN PIPE_RIGHT RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let id =
  let op = op0 in
       ( mk_ident("|>", rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN COLON_EQUALS RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let id =
  let op = op0 in
       ( mk_ident(":=", rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}
| LPAREN COLON_COLON RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let id =
  let op = op0 in
       ( mk_ident("::", rhs parseState 1) )
in
    ( {id with idText = compile_op' id.idText} )}

lidentOrUnderscore:
  IDENT
    {let id = $1 in
             ( mk_ident(id, rhs parseState 1))}
| UNDERSCORE
    {let _1 = () in
               ( gen (rhs parseState 1) )}

lident:
  IDENT
    {let id = $1 in
             ( mk_ident(id, rhs parseState 1))}

uident:
  NAME
    {let id = $1 in
            ( mk_ident(id, rhs parseState 1) )}

tvar:
  TVAR
    {let tv = $1 in
            ( mk_ident(tv, rhs parseState 1) )}

ascribeTyp:
  COLON tmArrow_tmNoEq_
    {let (_1, t) = ((), $2) in
                            ( t )}

ascribeKind:
  COLON kind
    {let (_1, k) = ((), $2) in
                  ( k )}

kind:
  tmArrow_tmNoEq_
    {let t = $1 in
                      ( {t with level=Kind} )}

term:
  noSeqTerm
    {let e = $1 in
      ( e )}
| noSeqTerm SEMICOLON term
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Seq(e1, e2)) (rhs2 parseState 1 3) Expr )}
| noSeqTerm SEMICOLON_SEMICOLON term
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Bind(gen (rhs parseState 1), e1, e2)) (rhs2 parseState 1 3) Expr )}
| lidentOrUnderscore LONG_LEFT_ARROW noSeqTerm SEMICOLON term
    {let (x, _2, e1, _4, e2) = ($1, (), $3, (), $5) in
      ( mk_term (Bind(x, e1, e2)) (rhs2 parseState 1 5) Expr )}

noSeqTerm:
  typ
    {let t = $1 in
           ( t )}
| tmIff SUBTYPE tmIff option___anonymous_5_
    {let (e, _2, t, tactic_opt) = ($1, (), $3, $4) in
      ( mk_term (Ascribed(e,{t with level=Expr},tactic_opt)) (rhs2 parseState 1 4) Expr )}
| atomicTermNotQUident DOT_LPAREN term RPAREN LARROW noSeqTerm
    {let (e1, _10, e0, _30, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".()", rhs parseState 1), e, rhs2 parseState 1 3 )
in
      (
        let (op, e2, _) = op_expr in
        mk_term (Op({op with idText = op.idText ^ "<-"}, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| atomicTermNotQUident DOT_LBRACK term RBRACK LARROW noSeqTerm
    {let (e1, _10, e0, _30, _3, e3) = ($1, (), $3, (), (), $6) in
let op_expr =
  let _3 = _30 in
  let e = e0 in
  let _1 = _10 in
                               ( mk_ident (".[]", rhs parseState 1), e, rhs2 parseState 1 3 )
in
      (
        let (op, e2, _) = op_expr in
        mk_term (Op({op with idText = op.idText ^ "<-"}, [ e1; e2; e3 ])) (rhs2 parseState 1 4) Expr
      )}
| REQUIRES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Requires(t, None)) (rhs2 parseState 1 2) Type_level )}
| ENSURES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Ensures(t, None)) (rhs2 parseState 1 2) Type_level )}
| ATTRIBUTES nonempty_list_atomicTerm_
    {let (_1, es) = ((), $2) in
      ( mk_term (Attributes es) (rhs2 parseState 1 2) Type_level )}
| IF noSeqTerm THEN noSeqTerm ELSE noSeqTerm
    {let (_1, e1, _3, e2, _5, e3) = ((), $2, (), $4, (), $6) in
      ( mk_term (If(e1, e2, e3)) (rhs2 parseState 1 6) Expr )}
| IF noSeqTerm THEN noSeqTerm
    {let (_1, e1, _3, e2) = ((), $2, (), $4) in
      (
        let e3 = mk_term (Const Const_unit) (rhs2 parseState 4 4) Expr in
        mk_term (If(e1, e2, e3)) (rhs2 parseState 1 4) Expr
      )}
| TRY term WITH reverse_left_flexible_nonempty_list_BAR_patternBranch_
    {let (_1, e1, _3, xs0) = ((), $2, (), $4) in
let pbs =
  let xs = xs0 in
     ( List.rev xs )
in
      (
         let branches = focusBranches (pbs) (rhs2 parseState 1 4) in
         mk_term (TryWith(e1, branches)) (rhs2 parseState 1 4) Expr
      )}
| MATCH term WITH reverse_left_flexible_list_BAR___anonymous_6_
    {let (_1, e, _3, xs0) = ((), $2, (), $4) in
let pbs =
  let xs = xs0 in
     ( List.rev xs )
in
      (
        let branches = focusBranches pbs (rhs2 parseState 1 4) in
        mk_term (Match(e, branches)) (rhs2 parseState 1 4) Expr
      )}
| LET OPEN quident IN term
    {let (_1, _2, uid, _4, e) = ($1, (), $3, (), $5) in
      ( mk_term (LetOpen(uid, e)) (rhs2 parseState 1 5) Expr )}
| LET letqualifier separated_nonempty_list_AND_letbinding_ IN term
    {let (_1, q, lbs, _4, e) = ($1, $2, $3, (), $5) in
      (
        let lbs = focusLetBindings lbs (rhs2 parseState 2 3) in
        mk_term (Let(q, lbs, e)) (rhs2 parseState 1 5) Expr
      )}
| FUNCTION reverse_left_flexible_nonempty_list_BAR_patternBranch_
    {let (_1, xs0) = ((), $2) in
let pbs =
  let xs = xs0 in
     ( List.rev xs )
in
      (
        let branches = focusBranches pbs (rhs2 parseState 1 2) in
        mk_function branches (lhs parseState) (rhs2 parseState 1 2)
      )}
| ASSUME atomicTerm
    {let (_1, e) = ((), $2) in
      ( let a = set_lid_range assume_lid (rhs parseState 1) in
        mkExplicitApp (mk_term (Var a) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2) )}
| lident LARROW noSeqTerm
    {let (id, _2, e) = ($1, (), $3) in
      ( mk_term (Assign(id, e)) (rhs2 parseState 1 3) Expr )}

typ:
  simpleTerm
    {let t = $1 in
                  ( t )}
| FORALL binders DOT trigger noSeqTerm
    {let (_10, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
let q =
  let _1 = _10 in
             ( fun x -> QForall x )
in
      (
        match bs with
            | [] -> raise (Error("Missing binders for a quantifier", rhs2 parseState 1 3))
            | _ -> mk_term (q (bs, trigger, e)) (rhs2 parseState 1 5) Formula
      )}
| EXISTS binders DOT trigger noSeqTerm
    {let (_10, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
let q =
  let _1 = _10 in
             ( fun x -> QExists x)
in
      (
        match bs with
            | [] -> raise (Error("Missing binders for a quantifier", rhs2 parseState 1 3))
            | _ -> mk_term (q (bs, trigger, e)) (rhs2 parseState 1 5) Formula
      )}

trigger:
  
    {      ( [] )}
| LBRACE_COLON_PATTERN disjunctivePats RBRACE
    {let (_1, pats, _3) = ((), $2, ()) in
                                                     ( pats )}

disjunctivePats:
  separated_nonempty_list_DISJUNCTION_conjunctivePat_
    {let pats = $1 in
                                                              ( pats )}

conjunctivePat:
  separated_nonempty_list_SEMICOLON_appTerm_
    {let pats = $1 in
                                                              ( pats )}

simpleTerm:
  tmIff
    {let e = $1 in
            ( e )}
| FUN nonempty_list_patternOrMultibinder_ RARROW term
    {let (_1, pats, _3, e) = ((), $2, (), $4) in
      ( mk_term (Abs(flatten pats, e)) (rhs2 parseState 1 4) Un )}

maybeFocusArrow:
  RARROW
    {let _1 = () in
                    ( false )}
| SQUIGGLY_RARROW
    {let _1 = () in
                    ( true )}

patternBranch:
  disjunctivePattern maybeFocusArrow term
    {let (pat, focus, e) = ($1, $2, $3) in
let when_opt =
                           ( None )
in
      (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 1)
        in
        (focus, (pat, when_opt, e))
      )}
| disjunctivePattern WHEN tmFormula maybeFocusArrow term
    {let (pat, _10, e0, focus, e) = ($1, (), $3, $4, $5) in
let when_opt =
  let e = e0 in
  let _1 = _10 in
                           ( Some e )
in
      (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 1)
        in
        (focus, (pat, when_opt, e))
      )}

tmIff:
  tmImplies IFF tmIff
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("<==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula )}
| tmImplies
    {let e = $1 in
                ( e )}

tmImplies:
  tmArrow_tmFormula_ IMPLIES tmImplies
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("==>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Formula )}
| tmArrow_tmFormula_
    {let e = $1 in
      ( e )}

tmArrow_tmFormula_:
  LPAREN aqual tmFormula RPAREN RARROW tmArrow_tmFormula_
    {let (_10, q0, dom_tm0, _40, _2, tgt) = ((), $2, $3, (), (), $6) in
let dom =
  let _4 = _40 in
  let dom_tm = dom_tm0 in
  let q = q0 in
  let _1 = _10 in
                                      ( Some q, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmFormula RARROW tmArrow_tmFormula_
    {let (dom_tm0, _2, tgt) = ($1, (), $3) in
let dom =
  let dom_tm = dom_tm0 in
  let aq_opt =
        ( None )
  in
                                      ( aq_opt, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual tmFormula RARROW tmArrow_tmFormula_
    {let (x00, dom_tm0, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let dom_tm = dom_tm0 in
  let x0 = x00 in
  let aq_opt =
    let x = x0 in
        ( Some x )
  in
                                      ( aq_opt, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmFormula
    {let e = $1 in
         ( e )}

tmArrow_tmNoEq_:
  LPAREN aqual tmNoEq RPAREN RARROW tmArrow_tmNoEq_
    {let (_10, q0, dom_tm0, _40, _2, tgt) = ((), $2, $3, (), (), $6) in
let dom =
  let _4 = _40 in
  let dom_tm = dom_tm0 in
  let q = q0 in
  let _1 = _10 in
                                      ( Some q, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmNoEq RARROW tmArrow_tmNoEq_
    {let (dom_tm0, _2, tgt) = ($1, (), $3) in
let dom =
  let dom_tm = dom_tm0 in
  let aq_opt =
        ( None )
  in
                                      ( aq_opt, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| aqual tmNoEq RARROW tmArrow_tmNoEq_
    {let (x00, dom_tm0, _2, tgt) = ($1, $2, (), $4) in
let dom =
  let dom_tm = dom_tm0 in
  let x0 = x00 in
  let aq_opt =
    let x = x0 in
        ( Some x )
  in
                                      ( aq_opt, dom_tm )
in
     (
       let (aq_opt, dom_tm) = dom in
       let b = match extract_named_refinement dom_tm with
         | None -> mk_binder (NoName dom_tm) (rhs parseState 1) Un aq_opt
         | Some (x, t, f) -> mkRefinedBinder x t true f (rhs2 parseState 1 1) aq_opt
       in
       mk_term (Product([b], tgt)) (rhs2 parseState 1 3)  Un
     )}
| tmNoEq
    {let e = $1 in
         ( e )}

tmFormula:
  tmFormula DISJUNCTION tmConjunction
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("\\/", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula )}
| tmConjunction
    {let e = $1 in
                    ( e )}

tmConjunction:
  tmConjunction CONJUNCTION tmTuple
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("/\\", rhs parseState 2), [e1;e2])) (rhs2 parseState 1 3) Formula )}
| tmTuple
    {let e = $1 in
              ( e )}

tmTuple:
  separated_nonempty_list_COMMA_tmEq_
    {let el = $1 in
      (
        match el with
          | [x] -> x
          | components -> mkTuple components (rhs2 parseState 1 1)
      )}

tmEq:
  tmEq EQUALS tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq COLON_EQUALS tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident(":=", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq PIPE_RIGHT tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("|>", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0a tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0b tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0c tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0d tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX1 tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX2 tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq MINUS tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(mk_ident("-", rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| MINUS tmEq
    {let (_1, e) = ((), $2) in
      ( mk_uminus e (rhs parseState 1) (rhs2 parseState 1 2) Expr )}
| tmNoEq
    {let e = $1 in
      ( e )}

tmNoEq:
  tmNoEq COLON_COLON tmNoEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( consTerm (rhs parseState 2) e1 e2 )}
| tmNoEq AMP tmNoEq
    {let (e1, _2, e2) = ($1, (), $3) in
      (
        let x, t, f = match extract_named_refinement e1 with
            | Some (x, t, f) -> x, t, f
            | _ -> raise (Error("Missing binder for the first component of a dependent tuple", rhs parseState 1)) in
        let dom = mkRefinedBinder x t true f (rhs parseState 1) None in
        let tail = e2 in
        let dom, res = match tail.tm with
            | Sum(dom', res) -> dom::dom', res
            | _ -> [dom], tail in
        mk_term (Sum(dom, res)) (rhs2 parseState 1 3) Type_level
      )}
| tmNoEq OPINFIX3 tmNoEq
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmNoEq BACKTICK qlident BACKTICK tmNoEq
    {let (e1, _2, id, _4, e2) = ($1, (), $3, (), $5) in
      ( mkApp (mk_term (Var id) (rhs2 parseState 2 4) Un) [ e1, Nothing; e2, Nothing ] (rhs2 parseState 1 5) )}
| tmNoEq OPINFIX4 tmNoEq
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(mk_ident(op, rhs parseState 2), [e1; e2])) (rhs2 parseState 1 3) Un)}
| lidentOrUnderscore COLON appTerm refineOpt
    {let (id, _2, e, phi_opt) = ($1, (), $3, $4) in
      (
        let t = match phi_opt with
          | None -> NamedTyp(id, e)
          | Some phi -> Refine(mk_binder (Annotated(id, e)) (rhs2 parseState 1 3) Type_level None, phi)
        in mk_term t (rhs2 parseState 1 4) Type_level
      )}
| LBRACE recordExp RBRACE
    {let (_1, e, _3) = ((), $2, ()) in
                              ( e )}
| TILDE atomicTerm
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident (op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Formula )}
| appTerm
    {let e = $1 in
              ( e )}

refineOpt:
  option___anonymous_7_
    {let phi_opt = $1 in
                                                    (phi_opt)}

recordExp:
  right_flexible_nonempty_list_SEMICOLON_simpleDef_
    {let record_fields = $1 in
      ( mk_term (Record (None, record_fields)) (rhs parseState 1) Expr )}
| appTerm WITH right_flexible_nonempty_list_SEMICOLON_simpleDef_
    {let (e, _2, record_fields) = ($1, (), $3) in
      ( mk_term (Record (Some e, record_fields)) (rhs2 parseState 1 3) Expr )}

simpleDef:
  qlident EQUALS noSeqTerm
    {let (x0, _20, y0) = ($1, (), $3) in
let e =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
                                                 ( e )}
| qlident
    {let lid = $1 in
                ( lid, mk_term (Name (lid_of_ids [ lid.ident ])) (rhs parseState 1) Un )}

appTerm:
  indexingTerm list_argTerm_
    {let (head, args) = ($1, $2) in
      ( mkApp head (map (fun (x,y) -> (y,x)) args) (rhs2 parseState 1 2) )}

argTerm:
  indexingTerm
    {let y0 = $1 in
let x =
  let y = y0 in
  let x =
             ( Nothing )
  in
      ( (x, y) )
in
                                    ( x )}
| HASH indexingTerm
    {let (_100, y0) = ((), $2) in
let x =
  let y = y0 in
  let _10 = _100 in
  let x =
    let _1 = _10 in
             ( Hash )
  in
      ( (x, y) )
in
                                    ( x )}
| universe
    {let u = $1 in
               ( u )}

indexingTerm:
  atomicTermNotQUident nonempty_list_dotOperator_
    {let (e1, op_exprs) = ($1, $2) in
      (
        List.fold_left (fun e1 (op, e2, r) ->
            mk_term (Op(op, [ e1; e2 ])) (union_ranges e1.range r) Expr)
            e1 op_exprs
      )}
| atomicTerm
    {let e = $1 in
    ( e )}

atomicTerm:
  atomicTermNotQUident
    {let x = $1 in
    ( x )}
| atomicTermQUident
    {let x = $1 in
    ( x )}
| opPrefixTerm_atomicTermQUident_
    {let x = $1 in
    ( x )}

atomicTermQUident:
  quident
    {let id = $1 in
    (
        let t = Name id in
        let e = mk_term t (rhs parseState 1) Un in
              e
    )}
| quident DOT_LPAREN term RPAREN
    {let (id, _2, t, _4) = ($1, (), $3, ()) in
    (
      mk_term (LetOpen (id, t)) (rhs2 parseState 1 4) Expr
    )}

atomicTermNotQUident:
  UNDERSCORE
    {let _1 = () in
               ( mk_term Wild (rhs parseState 1) Un )}
| ASSERT
    {let _1 = () in
             ( let a = set_lid_range assert_lid (rhs parseState 1) in
               mk_term (Var a) (rhs parseState 1) Expr )}
| tvar
    {let tv = $1 in
                ( mk_term (Tvar tv) (rhs parseState 1) Type_level )}
| constant
    {let c = $1 in
               ( mk_term (Const c) (rhs parseState 1) Expr )}
| L_TRUE
    {let _1 = () in
             ( mk_term (Name (lid_of_path ["True"] (rhs parseState 1))) (rhs parseState 1) Type_level )}
| L_FALSE
    {let _1 = () in
              ( mk_term (Name (lid_of_path ["False"] (rhs parseState 1))) (rhs parseState 1) Type_level )}
| opPrefixTerm_atomicTermNotQUident_
    {let x = $1 in
    ( x )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX3 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX4 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( mk_ident (op, rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX0a RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX0b RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX0c RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX0d RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX1 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX2 RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( mk_ident (op, rhs parseState 1) )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN PIPE_RIGHT RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident("|>", rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN COLON_EQUALS RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident(":=", rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN COLON_COLON RPAREN
    {let (_1, op0, _3) = ((), (), ()) in
let op =
  let op = op0 in
       ( mk_ident("::", rhs parseState 1) )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LENS_PAREN_LEFT tmEq COMMA separated_nonempty_list_COMMA_tmEq_ LENS_PAREN_RIGHT
    {let (_1, e0, _3, el, _5) = ((), $2, (), $4, ()) in
      ( mkDTuple (e0::el) (rhs2 parseState 1 5) )}
| projectionLHS list___anonymous_8_
    {let (e, field_projs) = ($1, $2) in
      ( fold_left (fun e lid -> mk_term (Project(e, lid)) (rhs2 parseState 1 2) Expr ) e field_projs )}
| BEGIN term END
    {let (_1, e, _3) = ((), $2, ()) in
      ( e )}

opPrefixTerm_atomicTermNotQUident_:
  OPPREFIX atomicTermNotQUident
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident(op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Expr )}

opPrefixTerm_atomicTermQUident_:
  OPPREFIX atomicTermQUident
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(mk_ident(op, rhs parseState 1), [e])) (rhs2 parseState 1 2) Expr )}

projectionLHS:
  qidentWithTypeArgs_qlident_option_fsTypeArgs__
    {let e = $1 in
      ( e )}
| qidentWithTypeArgs_quident_some_fsTypeArgs__
    {let e = $1 in
      ( e )}
| LPAREN term option_pair_hasSort_simpleTerm__ RPAREN
    {let (_1, e, sort_opt, _4) = ((), $2, $3, ()) in
      (
        let e1 = match sort_opt with
          | None -> e
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level},None)) (rhs2 parseState 1 4) level
        in mk_term (Paren e1) (rhs2 parseState 1 4) (e.level)
      )}
| LBRACK_BAR right_flexible_list_SEMICOLON_noSeqTerm_ BAR_RBRACK
    {let (_1, l0, _3) = ((), $2, ()) in
let es =
  let l = l0 in
                                                  ( l )
in
      (
        let l = mkConsList (rhs2 parseState 1 3) es in
        let pos = (rhs2 parseState 1 3) in
        mkExplicitApp (mk_term (Var (array_mk_array_lid)) pos Expr) [l] pos
      )}
| LBRACK right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l0, _3) = ((), $2, ()) in
let es =
  let l = l0 in
                                                  ( l )
in
      ( mkConsList (rhs2 parseState 1 3) es )}
| PERCENT_LBRACK right_flexible_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l0, _3) = ((), $2, ()) in
let es =
  let l = l0 in
                                                  ( l )
in
      ( mkLexList (rhs2 parseState 1 3) es )}
| BANG_LBRACE loption_separated_nonempty_list_COMMA_appTerm__ RBRACE
    {let (_1, xs0, _3) = ((), $2, ()) in
let es =
  let xs = xs0 in
      ( xs )
in
      ( mkRefSet (rhs2 parseState 1 3) es )}
| quident QMARK_DOT lident
    {let (ns, _2, id) = ($1, (), $3) in
      ( mk_term (Projector (ns, id)) (rhs2 parseState 1 3) Expr )}
| quident QMARK
    {let (lid, _2) = ($1, ()) in
      ( mk_term (Discrim lid) (rhs2 parseState 1 2) Un )}

fsTypeArgs:
  TYP_APP_LESS separated_nonempty_list_COMMA_atomicTerm_ TYP_APP_GREATER
    {let (_1, targs, _3) = ((), $2, ()) in
    (targs)}

qidentWithTypeArgs_qlident_option_fsTypeArgs__:
  qlident option_fsTypeArgs_
    {let (id, targs_opt) = ($1, $2) in
      (
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 2)
      )}

qidentWithTypeArgs_quident_some_fsTypeArgs__:
  quident some_fsTypeArgs_
    {let (id, targs_opt) = ($1, $2) in
      (
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 2)
      )}

hasSort:
  SUBKIND
    {let _1 = () in
            ( Type_level )}

constant:
  LPAREN_RPAREN
    {let _1 = () in
                  ( Const_unit )}
| INT
    {let n = $1 in
     (
        if snd n then
          errorR(Error("This number is outside the allowable range for representable integer constants", lhs(parseState)));
        Const_int (fst n, None)
     )}
| CHAR
    {let c = $1 in
           ( Const_char c )}
| STRING
    {let s = $1 in
             ( Const_string (s,lhs(parseState)) )}
| BYTEARRAY
    {let bs = $1 in
                 ( Const_bytearray (bs,lhs(parseState)) )}
| TRUE
    {let _1 = () in
         ( Const_bool true )}
| FALSE
    {let _1 = () in
          ( Const_bool false )}
| IEEE64
    {let f = $1 in
             ( Const_float f )}
| UINT8
    {let n = $1 in
            ( Const_int (n, Some (Unsigned, Int8)) )}
| INT8
    {let n = $1 in
      (
        if snd n then
          errorR(Error("This number is outside the allowable range for 8-bit signed integers", lhs(parseState)));
        Const_int (fst n, Some (Signed, Int8))
      )}
| UINT16
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int16)) )}
| INT16
    {let n = $1 in
      (
        if snd n then
          errorR(Error("This number is outside the allowable range for 16-bit signed integers", lhs(parseState)));
        Const_int (fst n, Some (Signed, Int16))
      )}
| UINT32
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int32)) )}
| INT32
    {let n = $1 in
      (
        if snd n then
          errorR(Error("This number is outside the allowable range for 32-bit signed integers", lhs(parseState)));
        Const_int (fst n, Some (Signed, Int32))
      )}
| UINT64
    {let n = $1 in
             ( Const_int (n, Some (Unsigned, Int64)) )}
| INT64
    {let n = $1 in
      (
        if snd n then
          errorR(Error("This number is outside the allowable range for 64-bit signed integers", lhs(parseState)));
        Const_int (fst n, Some (Signed, Int64))
      )}
| REIFY
    {let _1 = () in
            ( Const_reify )}

universe:
  UNIV_HASH atomicUniverse
    {let (_1, ua) = ((), $2) in
                                ( (UnivApp, ua) )}

universeFrom:
  atomicUniverse
    {let ua = $1 in
                      ( ua )}
| universeFrom OPINFIX2 universeFrom
    {let (u1, op_plus, u2) = ($1, $2, $3) in
       (
         if op_plus <> "+"
         then errorR(Error("The operator " ^ op_plus ^ " was found in universe context."
                           ^ "The only allowed operator in that context is +.",
                           rhs parseState 2)) ;
         mk_term (Op(mk_ident (op_plus, rhs parseState 2), [u1 ; u2])) (rhs2 parseState 1 3) Expr
       )}
| ident nonempty_list_atomicUniverse_
    {let (max, us) = ($1, $2) in
      (
        if text_of_id max <> text_of_lid max_lid
        then errorR(Error("A lower case ident " ^ text_of_id max ^
                          " was found in a universe context. " ^
                          "It should be either max or a universe variable 'usomething.",
                          rhs parseState 1)) ;
        let max = mk_term (Var (lid_of_ids [max])) (rhs parseState 1) Expr in
        mkApp max (map (fun u -> u, Nothing) us) (rhs2 parseState 1 2)
      )}

atomicUniverse:
  UNDERSCORE
    {let _1 = () in
      ( mk_term Wild (rhs parseState 1) Expr )}
| INT
    {let n = $1 in
      (
        if snd n then
          errorR(Error("This number is outside the allowable range for representable integer constants",
                       lhs(parseState)));
        mk_term (Const (Const_int (fst n, None))) (rhs parseState 1) Expr
      )}
| lident
    {let u = $1 in
             ( mk_term (Uvar u) u.idRange Expr )}
| LPAREN universeFrom RPAREN
    {let (_1, u, _3) = ((), $2, ()) in
    ( u (*mk_term (Paren u) (rhs2 parseState 1 3) Expr*) )}

some_fsTypeArgs_:
  fsTypeArgs
    {let x = $1 in
        ( Some x )}

right_flexible_list_SEMICOLON_noSeqTerm_:
  
    {        ( [] )}
| noSeqTerm
    {let x = $1 in
        ( [x] )}
| noSeqTerm SEMICOLON right_flexible_list_SEMICOLON_noSeqTerm_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_list_SEMICOLON_recordFieldDecl_:
  
    {        ( [] )}
| recordFieldDecl
    {let x = $1 in
        ( [x] )}
| recordFieldDecl SEMICOLON right_flexible_list_SEMICOLON_recordFieldDecl_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_list_SEMICOLON_simpleDef_:
  
    {        ( [] )}
| simpleDef
    {let x = $1 in
        ( [x] )}
| simpleDef SEMICOLON right_flexible_list_SEMICOLON_simpleDef_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_nonempty_list_SEMICOLON_recordFieldDecl_:
  recordFieldDecl
    {let x = $1 in
        ( [x] )}
| recordFieldDecl SEMICOLON right_flexible_list_SEMICOLON_recordFieldDecl_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

right_flexible_nonempty_list_SEMICOLON_simpleDef_:
  simpleDef
    {let x = $1 in
        ( [x] )}
| simpleDef SEMICOLON right_flexible_list_SEMICOLON_simpleDef_
    {let (x, _2, xs) = ($1, (), $3) in
                                           ( x :: xs )}

reverse_left_flexible_list_BAR___anonymous_6_:
  
    {   ( [] )}
| patternBranch
    {let pb0 = $1 in
let x =
  let pb = pb0 in
                                                                     (pb)
in
   ( [x] )}
| reverse_left_flexible_list_BAR___anonymous_6_ BAR patternBranch
    {let (xs, _2, pb0) = ($1, (), $3) in
let x =
  let pb = pb0 in
                                                                     (pb)
in
   ( x :: xs )}

reverse_left_flexible_nonempty_list_BAR_patternBranch_:
  patternBranch
    {let x = $1 in
let _1 =
      ( None )
in
   ( [x] )}
| BAR patternBranch
    {let (x0, x) = ((), $2) in
let _1 =
  let x = x0 in
      ( Some x )
in
   ( [x] )}
| reverse_left_flexible_nonempty_list_BAR_patternBranch_ BAR patternBranch
    {let (xs, _2, x) = ($1, (), $3) in
   ( x :: xs )}

%%




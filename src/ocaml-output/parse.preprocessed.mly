%{

(* (c) Microsoft Corporation. All rights reserved *)

(* TO BE ADDED IN parse.fsy
open Prims
open FStar.List
open FStar.Util
open FStar.Range
open FStar.Options
open FStar.Absyn.Syntax
open FStar.Absyn.Const
open FStar.Absyn.Util
open FStar.Parser.AST
open FStar.Parser.Util
open FStar.Const
open FStar.Ident
*)

open Prims
open FStar_List
open FStar_Util
open FStar_Range
open FStar_Options
open FStar_Absyn_Syntax
open FStar_Absyn_Const
open FStar_Absyn_Util
open FStar_Parser_AST
open FStar_Parser_Util
open FStar_Const
open FStar_Ident

let as_frag d ds =
    let rec as_mlist out ((m,r,doc), cur) ds =
    match ds with
    | [] -> List.rev (Module(m, (mk_decl (TopLevelModule(m)) r doc) ::(List.rev cur))::out)
    | d::ds ->
      begin match d.d with
        | TopLevelModule m' ->
				as_mlist (Module(m, (mk_decl (TopLevelModule(m)) r doc) :: (List.rev cur))::out) ((m',d.drange,d.doc), []) ds
        | _ -> as_mlist out ((m,r,doc), d::cur) ds
      end in
    match d.d with
    | TopLevelModule m ->
        let ms = as_mlist [] ((m,d.drange,d.doc), []) ds in
        begin match ms with
        | _::Module(n, _)::_ ->
		(* This check is coded to hard-fail in dep.num_of_toplevelmods. *)
        let msg = "Support for more than one module in a file is deprecated" in
        print2_warning "%s (Warning): %s\n" (string_of_range (range_of_lid n)) msg
        | _ -> ()
        end;
        Inl ms
    | _ ->
        let ds = d::ds in
        iter (function {d=TopLevelModule _; drange=r} -> raise (Error("Unexpected module declaration", r))
                       | _ -> ()) ds;
        Inr ds

%}
%start inputFragment
%start term
%token ABSTRACT
%token ACTIONS
%token AMP
%token AND
%token ASSERT
%token ASSUME
%token BACKTICK
%token BANG_LBRACE
%token BAR
%token BAR_RBRACK
%token BEGIN
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
%token INLINE
%token INLINE_FOR_EXTRACTION
%token <string * bool> INT
%token <string * bool> INT16
%token <string * bool> INT32
%token <string * bool> INT64
%token <string * bool> INT8
%token IRREDUCIBLE
%token KIND
%token LARROW
%token LBRACE
%token LBRACE_COLON_PATTERN
%token LBRACK
%token LBRACK_BAR
%token LENS_PAREN_LEFT
%token LENS_PAREN_RIGHT
%token <bool> LET
%token LOGIC
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
%token NEW_EFFECT_FOR_FREE
%token NOEQUALITY
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
%token UNOPTEQUALITY
%token VAL
%token WHEN
%token WITH
%nonassoc THEN
%nonassoc ELSE
%right IFF
%right IMPLIES
%left DISJUNCTION
%left CONJUNCTION
%right COMMA
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
%type <FStar_Ident.ident> ident
%type <inputFragment> inputFragment
%type <term> term
%%

option_FSDOC_:
  
    {    ( None )}
| FSDOC
    {let x = $1 in
    ( Some x )}

option___anonymous_0_:
  
    {    ( None )}
| PRAGMALIGHT STRING
    {let (_10, _20) = ((), $2) in
let x =
  let _2 = _20 in
  let _1 = _10 in
                                ()
in
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

option___anonymous_7_:
  
    {    ( None )}
| TYP_APP_LESS separated_nonempty_list_COMMA_atomicTerm_ TYP_APP_GREATER
    {let (_10, targs0, _30) = ((), $2, ()) in
let x =
  let _3 = _30 in
  let targs = targs0 in
  let _1 = _10 in
                                                                                                                    (targs)
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

loption_separated_nonempty_list_COMMA_appTerm__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_appTerm_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_SEMICOLON_effectDecl__:
  
    {    ( [] )}
| separated_nonempty_list_SEMICOLON_effectDecl_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_SEMICOLON_openPatternRec1__:
  
    {    ( [] )}
| separated_nonempty_list_SEMICOLON_openPatternRec1_
    {let x = $1 in
    ( x )}

list___anonymous_3_:
  
    {    ( [] )}
| AND maybeFocus letbinding list___anonymous_3_
    {let (_10, x00, y00, xs) = ((), $2, $3, $4) in
let x =
  let y0 = y00 in
  let x0 = x00 in
  let _1 = _10 in
  let p =
    let y = y0 in
    let x = x0 in
        ( (x, y) )
  in
                                                 (p)
in
    ( x :: xs )}

list___anonymous_6_:
  
    {    ( [] )}
| DOT lid list___anonymous_6_
    {let (_10, id0, xs) = ((), $2, $3) in
let x =
  let id = id0 in
  let _1 = _10 in
                                                  (id)
in
    ( x :: xs )}

list_binder_:
  
    {    ( [] )}
| binder list_binder_
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

list_pair_maybeHash_indexingTerm__:
  
    {    ( [] )}
| indexingTerm list_pair_maybeHash_indexingTerm__
    {let (y0, xs) = ($1, $2) in
let x =
  let y = y0 in
  let x =
             ( Nothing )
  in
      ( (x, y) )
in
    ( x :: xs )}
| HASH indexingTerm list_pair_maybeHash_indexingTerm__
    {let (_100, y0, xs) = ((), $2, $3) in
let x =
  let y = y0 in
  let _10 = _100 in
  let x =
    let _1 = _10 in
             ( Hash )
  in
      ( (x, y) )
in
    ( x :: xs )}

list_patternBranch_:
  
    {    ( [] )}
| patternBranch list_patternBranch_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

list_qualifier_:
  
    {    ( [] )}
| qualifier list_qualifier_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_bindingPattern_:
  bindingPattern
    {let x = $1 in
    ( [ x ] )}
| bindingPattern nonempty_list_bindingPattern_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_patternRec_:
  patternRec
    {let x = $1 in
    ( [ x ] )}
| patternRec nonempty_list_patternRec_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

nonempty_list_qualId_:
  qualId
    {let x = $1 in
    ( [ x ] )}
| qualId nonempty_list_qualId_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

separated_nonempty_list_AND_pair_option_FSDOC__tyconDefinition__:
  option_FSDOC_ tyconDefinition
    {let (x0, y0) = ($1, $2) in
let x =
  let y = y0 in
  let x = x0 in
      ( (x, y) )
in
    ( [ x ] )}
| option_FSDOC_ tyconDefinition AND separated_nonempty_list_AND_pair_option_FSDOC__tyconDefinition__
    {let (x0, y0, _2, xs) = ($1, $2, (), $4) in
let x =
  let y = y0 in
  let x = x0 in
      ( (x, y) )
in
    ( x :: xs )}

separated_nonempty_list_BAR_pattern_:
  pattern
    {let x = $1 in
    ( [ x ] )}
| pattern BAR separated_nonempty_list_BAR_pattern_
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

separated_nonempty_list_COMMA_openPatternRec2_:
  openPatternRec2
    {let x = $1 in
    ( [ x ] )}
| openPatternRec2 COMMA separated_nonempty_list_COMMA_openPatternRec2_
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

separated_nonempty_list_SEMICOLON_openPatternRec1_:
  openPatternRec1
    {let x = $1 in
    ( [ x ] )}
| openPatternRec1 SEMICOLON separated_nonempty_list_SEMICOLON_openPatternRec1_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_SEMICOLON_separated_pair_lid_EQUALS_openPatternRec1__:
  lid EQUALS openPatternRec1
    {let (x0, _20, y0) = ($1, (), $3) in
let x =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
    ( [ x ] )}
| lid EQUALS openPatternRec1 SEMICOLON separated_nonempty_list_SEMICOLON_separated_pair_lid_EQUALS_openPatternRec1__
    {let (x0, _20, y0, _2, xs) = ($1, (), $3, (), $5) in
let x =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
    ( x :: xs )}

inputFragment:
  option___anonymous_0_ decl list_decl_ option_mainDecl_ EOF
    {let (_1, d, decls, main_opt, _5) = ($1, $2, $3, $4, ()) in
       (
         let decls = match main_opt with
           | None -> decls
           | Some main -> decls @ [main]
         in as_frag d decls
       )}

mainDecl:
  SEMICOLON_SEMICOLON option_FSDOC_ term
    {let (_1, doc_opt, t) = ((), $2, $3) in
      ( mk_decl (Main t) (rhs2 parseState 1 3) doc_opt )}

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

decl:
  option_FSDOC_ decl2
    {let (fsdoc_opt, decl) = ($1, $2) in
                                ( mk_decl decl (rhs parseState 2) fsdoc_opt )}

decl2:
  OPEN qname
    {let (_1, uid) = ((), $2) in
      ( Open uid )}
| MODULE name EQUALS qname
    {let (_1, uid1, _3, uid2) = ((), $2, (), $4) in
      (  ModuleAbbrev(uid1, uid2) )}
| MODULE qname
    {let (_1, uid) = ((), $2) in
      (  TopLevelModule uid )}
| kind_abbrev
    {let k = $1 in
      ( k )}
| tycon
    {let t = $1 in
      ( t )}
| list_qualifier_ LET letqualifier letbinding letbindings
    {let (qs0, _2, lq, lb, lbs) = ($1, $2, $3, $4, $5) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      (
        let r, focus = lq in
        let lbs = focusLetBindings ((focus, lb)::lbs) (rhs2 parseState 1 5) in
        ToplevelLet(qs, r, lbs)
      )}
| list_qualifier_ VAL ident COLON typ
    {let (qs0, _2, lid, _4, t) = ($1, (), $3, (), $5) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( Val(qs, lid, t) )}
| assumeTag name COLON noSeqTerm
    {let (tag, lid, _3, e0) = ($1, $2, (), $4) in
let phi =
  let e = e0 in
                  ( {e with level=Formula} )
in
      ( Assume(tag, lid, phi) )}
| EXCEPTION name option___anonymous_1_
    {let (_1, lid, t_opt) = ((), $2, $3) in
      ( Exception(lid, t_opt) )}
| list_qualifier_ NEW_EFFECT newEffect
    {let (qs0, _2, ne) = ($1, (), $3) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( NewEffect (qs, ne) )}
| list_qualifier_ SUB_EFFECT subEffect
    {let (qs0, _2, se) = ($1, (), $3) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( SubEffect se )}
| list_qualifier_ NEW_EFFECT_FOR_FREE newEffect
    {let (qs0, _2, ne) = ($1, (), $3) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( NewEffectForFree (qs, ne) )}
| pragma
    {let p = $1 in
      ( Pragma p )}
| FSDOC_STANDALONE
    {let doc = $1 in
      ( Fsdoc doc )}

tycon:
  list_qualifier_ TYPE separated_nonempty_list_AND_pair_option_FSDOC__tyconDefinition__
    {let (qs0, _2, tcdefs) = ($1, (), $3) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( Tycon (qs, List.map (fun (doc, f) -> (f false, doc)) tcdefs) )}
| list_qualifier_ EFFECT tyconDefinition
    {let (qs0, _2, tcdef) = ($1, (), $3) in
let qs =
  let qs = qs0 in
                         ( qs )
in
      ( Tycon(Effect::qs, [(tcdef true, None)]) )}

tyconDefinition:
  eitherName typars option_ascribeKind_ tyconDefn
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

tyconDefn:
  
    {      ( (fun id binders kopt eff -> if not eff then check_id id; TyconAbstract(id, binders, kopt)) )}
| EQUALS typ
    {let (_1, t) = ((), $2) in
      ( (fun id binders kopt eff -> if not eff then check_id id; TyconAbbrev(id, binders, kopt, t)) )}
| EQUALS LBRACE ident COLON typ recordFieldDecls RBRACE
    {let (_1, _2, x0, _20, y0, record_field_decls, _5) = ((), (), $3, (), $5, $6, ()) in
let decl0 =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
   (
     let (lid, t) = decl0 in
     (fun id binders kopt eff ->
       if not eff then check_id id; TyconRecord(id, binders, kopt, (lid, t, None)::record_field_decls))
   )}
| EQUALS list_constructorDecl_
    {let (_1, ct_decls) = ((), $2) in
      ( (fun id binders kopt eff -> if not eff then check_id id; TyconVariant(id, binders, kopt, ct_decls)) )}

recordFieldDecls:
  
    {let _1 =
      ( None )
in
                       ( [] )}
| SEMICOLON
    {let x0 = () in
let _1 =
  let x = x0 in
      ( Some x )
in
                       ( [] )}
| SEMICOLON ident COLON typ recordFieldDecls
    {let (_1, lid, _4, t, decls) = ((), $2, (), $4, $5) in
let doc_opt =
      ( None )
in
      ( (lid, t, doc_opt)::decls )}
| SEMICOLON FSDOC ident COLON typ recordFieldDecls
    {let (_1, x0, lid, _4, t, decls) = ((), $2, $3, (), $5, $6) in
let doc_opt =
  let x = x0 in
      ( Some x )
in
      ( (lid, t, doc_opt)::decls )}

constructorDecl:
  BAR option_FSDOC_ name COLON typ
    {let (_1, doc_opt, uid, _4, t) = ((), $2, $3, (), $5) in
                                                           ( (uid, Some t, doc_opt, false) )}
| BAR option_FSDOC_ name option___anonymous_2_
    {let (_1, doc_opt, uid, t_opt) = ((), $2, $3, $4) in
                                                           ( (uid, t_opt, doc_opt, true) )}

kind_abbrev:
  KIND eitherName binders EQUALS kind
    {let (_1, lid, bs, _4, k) = ((), $2, $3, (), $5) in
      ( KindAbbrev(lid, bs, k) )}

letbindings:
  list___anonymous_3_
    {let lbs = $1 in
                                                    ( lbs )}

letbinding:
  ident nonempty_list_bindingPattern_ option_ascribeTyp_ EQUALS term
    {let (lid, lbp, ascr_opt, _4, tm) = ($1, $2, $3, (), $5) in
      (
        let pat = mk_pattern (PatVar(lid, None)) (rhs parseState 1) in
        let pat = mk_pattern (PatApp (pat, flatten lbp)) (rhs2 parseState 1 2) in
        let pos = rhs2 parseState 1 5 in
        match ascr_opt with
        | None -> (pat, tm)
        | Some t -> (mk_pattern (PatAscribed(pat, t)) pos, tm)
      )}
| pattern ascribeTyp EQUALS term
    {let (pat, ascr, _3, tm) = ($1, $2, (), $4) in
      ( (mk_pattern (PatAscribed(pat, ascr)) (rhs2 parseState 1 4), tm) )}
| pattern EQUALS term
    {let (pat, _2, tm) = ($1, (), $3) in
      ( (pat, tm) )}

newEffect:
  effectRedefinition
    {let ed = $1 in
       ( ed )}
| effectDefinition
    {let ed = $1 in
       ( ed )}

effectRedefinition:
  name EQUALS simpleTerm
    {let (lid, _2, t) = ($1, (), $3) in
      ( RedefineEffect(lid, [], t) )}

effectDefinition:
  LBRACE name binders COLON kind WITH separated_nonempty_list_SEMICOLON_effectDecl_ actionDecls RBRACE
    {let (_1, lid, bs, _4, k, _6, eds, actions, _9) = ((), $2, $3, (), $5, (), $7, $8, ()) in
      (
         DefineEffect(lid, bs, k, eds, actions)
      )}

actionDecls:
  
    {      ( [] )}
| AND ACTIONS loption_separated_nonempty_list_SEMICOLON_effectDecl__
    {let (_1, _2, xs0) = ((), (), $3) in
let actions =
  let xs = xs0 in
      ( xs )
in
      ( actions )}

effectDecl:
  ident EQUALS simpleTerm
    {let (lid, _2, t) = ($1, (), $3) in
     ( mk_decl (Tycon ([], [(TyconAbbrev(lid, [], None, t), None)])) (rhs2 parseState 1 3) None )}

subEffect:
  qname SQUIGGLY_RARROW qname EQUALS simpleTerm
    {let (src_eff, _2, tgt_eff, _4, lift) = ($1, (), $3, (), $5) in
      ( { msource = src_eff; mdest = tgt_eff; lift_op = NonReifiableLift lift } )}
| qname SQUIGGLY_RARROW qname LBRACE IDENT EQUALS simpleTerm RBRACE
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
| qname SQUIGGLY_RARROW qname LBRACE IDENT EQUALS simpleTerm SEMICOLON IDENT EQUALS simpleTerm RBRACE
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
    (* KM : We are raising before returning some value ? *)
    raise (Error("The 'inline' qualifier has been renamed to 'unfold'", lhs parseState));
	  Inline
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

assumeTag:
  ASSUME
    {let _1 = () in
           ( [Assumption] )}

maybeFocus:
  boption_SQUIGGLY_RARROW_
    {let b = $1 in
                               ( b )}

letqualifier:
  maybeFocus REC
    {let (b, _2) = ($1, ()) in
                        ( Rec, b )}
| MUTABLE
    {let _1 = () in
                        ( Mutable, false )}
| 
    {                        ( NoLetQualifier, false )}

aqual:
  EQUALS
    {let _1 = () in
              ( if universes()
                then print1 "%s (Warning): The '=' notation for equality constraints on binders is deprecated; use '$' instead\n" (string_of_range (lhs parseState));
				        Equality )}
| aqual_universes
    {let q = $1 in
                      ( q )}

aqual_universes:
  HASH
    {let _1 = () in
              ( Implicit )}
| DOLLAR
    {let _1 = () in
              ( Equality )}

pattern:
  openPatternRec1
    {let pat = $1 in
                        ( pat )}

openPatternRec1:
  separated_nonempty_list_COMMA_openPatternRec2_
    {let pats = $1 in
      ( match pats with | [x] -> x | l -> mk_pattern (PatTuple (l, false)) (rhs parseState 1) )}

openPatternRec2:
  openPatternRec2 COLON_COLON openPatternRec2
    {let (pat, _2, pats) = ($1, (), $3) in
      ( mk_pattern (consPat (rhs parseState 3) pat pats) (rhs2 parseState 1 3) )}
| qname nonempty_list_patternRec_
    {let (uid, args) = ($1, $2) in
      (
        let head_pat = mk_pattern (PatName uid) (rhs parseState 1) in
        mk_pattern (PatApp (head_pat, args)) (rhs2 parseState 1 2)
      )}
| patternRec
    {let pat = $1 in
      ( pat )}

patternRec:
  LPAREN pattern COLON typ refineOpt RPAREN
    {let (_1, pat, _3, t, phi_opt, _6) = ((), $2, (), $4, $5, ()) in
      (
        let pos_t = rhs2 parseState 2 4 in
        let pos = rhs2 parseState 1 6 in
        mkRefinedPattern pat t true phi_opt pos_t pos
      )}
| LBRACK loption_separated_nonempty_list_SEMICOLON_openPatternRec1__ RBRACK
    {let (_1, xs0, _3) = ((), $2, ()) in
let pats =
  let xs = xs0 in
      ( xs )
in
      ( mk_pattern (PatList pats) (rhs2 parseState 1 3) )}
| LBRACE separated_nonempty_list_SEMICOLON_separated_pair_lid_EQUALS_openPatternRec1__ RBRACE
    {let (_1, record_pat, _3) = ((), $2, ()) in
      ( mk_pattern (PatRecord record_pat) (rhs2 parseState 1 4) )}
| LENS_PAREN_LEFT openPatternRec2 COMMA separated_nonempty_list_COMMA_openPatternRec2_ LENS_PAREN_RIGHT
    {let (_1, pat0, _3, pats, _5) = ((), $2, (), $4, ()) in
      ( mk_pattern (PatTuple(pat0::pats, true)) (rhs2 parseState 1 5) )}
| LPAREN pattern RPAREN
    {let (_1, pat, _3) = ((), $2, ()) in
                                ( pat )}
| tvar
    {let tv = $1 in
                              ( mk_pattern (PatTvar (tv, None)) (rhs parseState 1) )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX3 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX4 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| LPAREN OPINFIX0a RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
  in
       ( op )
in
      ( mk_pattern (PatOp op) (rhs2 parseState 1 3) )}
| UNDERSCORE
    {let _1 = () in
      ( mk_pattern PatWild (rhs parseState 1) )}
| constant
    {let c = $1 in
      ( mk_pattern (PatConst c) (rhs parseState 1) )}
| qualId
    {let qual_id = $1 in
      ( mk_pattern (PatVar (snd qual_id, fst qual_id)) (rhs parseState 1) )}
| qname
    {let uid = $1 in
      ( mk_pattern (PatName uid) (rhs parseState 1) )}

disjunctivePattern:
  separated_nonempty_list_BAR_pattern_
    {let pats = $1 in
                                               ( pats )}

bindingPattern:
  patternRec
    {let pat = $1 in
                   ( [pat] )}
| LPAREN qualId nonempty_list_qualId_ COLON typ refineOpt RPAREN
    {let (_1, qual_id0, qual_ids, _4, t, r, _7) = ((), $2, $3, (), $5, $6, ()) in
      (
        let pos = rhs2 parseState 1 6 in
        let t_pos = rhs parseState 4 in
        let qual_ids = qual_id0 :: qual_ids in
        List.map (fun (q, x) -> mkRefinedPattern (mk_pattern (PatVar (x, q)) pos) t false r t_pos pos) qual_ids
      )}

binder:
  ident
    {let lid = $1 in
              ( [mk_binder (Variable lid) (rhs parseState 1) Type None]  )}
| tvar
    {let tv = $1 in
             ( [mk_binder (TVariable tv) (rhs parseState 1) Kind None]  )}
| LPAREN nonempty_list_qualId_ COLON typ refineOpt RPAREN
    {let (_1, qual_ids, _3, t, r, _6) = ((), $2, (), $4, $5, ()) in
     (
       let should_bind_var = match qual_ids with | [ _ ] -> true | _ -> false in
       List.map (fun (q, x) -> mkRefinedBinder x t should_bind_var r (rhs2 parseState 1 5) q) qual_ids
     )}

binders:
  list_binder_
    {let bs = $1 in
                         ( flatten bs )}

qualId:
  ident
    {let y0 = $1 in
let x =
  let y = y0 in
  let x =
        ( None )
  in
      ( (x, y) )
in
                                                ( x )}
| aqual_universes ident
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

lid:
  path_ident_
    {let ids = $1 in
                    ( lid_of_ids ids )}

qname:
  path_name_
    {let ids = $1 in
                   ( lid_of_ids ids )}

eitherQname:
  path_eitherName_
    {let ids = $1 in
                         ( lid_of_ids ids )}

path_eitherName_:
  eitherName
    {let id = $1 in
          ( [id] )}
| name DOT path_eitherName_
    {let (uid, _2, p) = ($1, (), $3) in
                            ( uid::p )}

path_ident_:
  ident
    {let id = $1 in
          ( [id] )}
| name DOT path_ident_
    {let (uid, _2, p) = ($1, (), $3) in
                            ( uid::p )}

path_name_:
  name
    {let id = $1 in
          ( [id] )}
| name DOT path_name_
    {let (uid, _2, p) = ($1, (), $3) in
                            ( uid::p )}

eitherName:
  ident
    {let x = $1 in
            ( x )}
| name
    {let x = $1 in
            ( x )}

ident:
  IDENT
    {let id = $1 in
             ( mk_ident(id, rhs parseState 1))}

name:
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

typ:
  simpleTerm
    {let t = $1 in
                  ( t )}
| FORALL binders DOT qpat noSeqTerm
    {let (_1, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
      (
        match bs with
            | [] -> raise (Error("Missing binders for a quantifier", rhs2 parseState 1 3))
            | _ -> mk_term (QForall(bs, trigger, e)) (rhs2 parseState 1 5) Formula
      )}
| EXISTS binders DOT qpat noSeqTerm
    {let (_1, bs, _3, trigger, e) = ((), $2, (), $4, $5) in
      (
        match bs with
            | [] -> raise (Error("Missing binders for a quantifier", rhs2 parseState 1 3))
            | _ -> mk_term (QExists(bs, trigger, e)) (rhs2 parseState 1 5) Formula
      )}

term:
  noSeqTerm
    {let e = $1 in
      ( e )}
| noSeqTerm SEMICOLON term
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Seq(e1, e2)) (rhs2 parseState 1 3) Expr )}

noSeqTerm:
  typ
    {let t = $1 in
           ( t )}
| atomicTerm DOT_LBRACK term RBRACK LARROW noSeqTerm
    {let (e1, _2, e2, _4, _5, e3) = ($1, (), $3, (), (), $6) in
      ( mk_term (Op(".[]<-", [ e1; e2; e3 ])) (rhs2 parseState 1 6) Expr )}
| atomicTerm DOT_LPAREN term RPAREN LARROW noSeqTerm
    {let (e1, _2, e2, _4, _5, e3) = ($1, (), $3, (), (), $6) in
      ( mk_term (Op(".()<-", [ e1; e2; e3 ])) (rhs2 parseState 1 6) Expr )}
| REQUIRES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Requires(t, None)) (rhs2 parseState 1 2) Type )}
| ENSURES typ
    {let (_1, t) = ((), $2) in
      ( mk_term (Ensures(t, None)) (rhs2 parseState 1 2) Type )}
| IF noSeqTerm THEN noSeqTerm ELSE noSeqTerm
    {let (_1, e1, _3, e2, _5, e3) = ((), $2, (), $4, (), $6) in
      ( mk_term (If(e1, e2, e3)) (rhs2 parseState 1 6) Expr )}
| IF noSeqTerm THEN noSeqTerm
    {let (_1, e1, _3, e2) = ((), $2, (), $4) in
      (
        let e3 = mk_term (Const Const_unit) (rhs2 parseState 4 4) Expr in
        mk_term (If(e1, e2, e3)) (rhs2 parseState 1 4) Expr
      )}
| TRY term WITH firstPatternBranch patternBranches
    {let (_1, e1, _3, pb, pbs) = ((), $2, (), $4, $5) in
      (
         let branches = focusBranches (pb::pbs) (rhs2 parseState 1 5) in
         mk_term (TryWith(e1, branches)) (rhs2 parseState 1 5) Expr
      )}
| MATCH term WITH patternBranches
    {let (_1, e, _3, pbs) = ((), $2, (), $4) in
      (
        let branches = focusBranches pbs (rhs2 parseState 1 4) in
        mk_term (Match(e, branches)) (rhs2 parseState 1 4) Expr
      )}
| LET OPEN qname IN term
    {let (_1, _2, uid, _4, e) = ($1, (), $3, (), $5) in
      ( mk_term (LetOpen(uid, e)) (rhs2 parseState 1 5) Expr )}
| LET letqualifier letbinding letbindings IN term
    {let (_1, q, lb, lbs, _5, e) = ($1, $2, $3, $4, (), $6) in
      (
        let r, focus = q in
        let lbs = focusLetBindings ((focus,lb)::lbs) (rhs2 parseState 2 4) in
        mk_term (Let(r, lbs, e)) (rhs2 parseState 1 6) Expr
      )}
| FUNCTION firstPatternBranch patternBranches
    {let (_1, pb, pbs) = ((), $2, $3) in
      (
        let branches = focusBranches (pb::pbs) (rhs2 parseState 1 3) in
        mk_function branches (lhs parseState) (rhs2 parseState 1 3)
      )}
| ASSUME atomicTerm
    {let (_1, e) = ((), $2) in
      ( mkExplicitApp (mk_term (Var assume_lid) (rhs parseState 1) Expr) [e] (rhs2 parseState 1 2) )}
| ident LARROW noSeqTerm
    {let (id, _2, e) = ($1, (), $3) in
      ( mk_term (Assign(id, e)) (rhs2 parseState 1 3) Expr )}

qpat:
  
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
| FUN nonempty_list_bindingPattern_ RARROW term
    {let (_1, pats, _3, e) = ((), $2, (), $4) in
      ( mk_term (Abs(flatten pats, e)) (rhs2 parseState 1 4) Un )}

patternBranches:
  list_patternBranch_
    {let pbs = $1 in
                            ( pbs )}

maybeFocusArrow:
  RARROW
    {let _1 = () in
                    ( false )}
| SQUIGGLY_RARROW
    {let _1 = () in
                    ( true )}

firstPatternBranch:
  disjunctivePattern maybeFocusArrow term
    {let (pat0, focus0, e0) = ($1, $2, $3) in
let pb =
  let e = e0 in
  let focus = focus0 in
  let pat = pat0 in
  let when_opt =
                             ( None )
  in
  let _1 =
        ( None )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                                      ( pb )}
| disjunctivePattern WHEN tmFormula maybeFocusArrow term
    {let (pat0, _100, e00, focus0, e1) = ($1, (), $3, $4, $5) in
let pb =
  let e = e1 in
  let focus = focus0 in
  let e0 = e00 in
  let _10 = _100 in
  let pat = pat0 in
  let when_opt =
    let e = e0 in
    let _1 = _10 in
                             ( Some e )
  in
  let _1 =
        ( None )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                                      ( pb )}
| BAR disjunctivePattern maybeFocusArrow term
    {let (x00, pat0, focus0, e0) = ((), $2, $3, $4) in
let pb =
  let e = e0 in
  let focus = focus0 in
  let pat = pat0 in
  let x0 = x00 in
  let when_opt =
                             ( None )
  in
  let _1 =
    let x = x0 in
        ( Some x )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                                      ( pb )}
| BAR disjunctivePattern WHEN tmFormula maybeFocusArrow term
    {let (x00, pat0, _100, e00, focus0, e1) = ((), $2, (), $4, $5, $6) in
let pb =
  let e = e1 in
  let focus = focus0 in
  let e0 = e00 in
  let _10 = _100 in
  let pat = pat0 in
  let x0 = x00 in
  let when_opt =
    let e = e0 in
    let _1 = _10 in
                             ( Some e )
  in
  let _1 =
    let x = x0 in
        ( Some x )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                                      ( pb )}

patternBranch:
  BAR disjunctivePattern maybeFocusArrow term
    {let (_10, pat0, focus0, e0) = ((), $2, $3, $4) in
let pb =
  let e = e0 in
  let focus = focus0 in
  let pat = pat0 in
  let _1 = _10 in
  let when_opt =
                             ( None )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                             ( pb )}
| BAR disjunctivePattern WHEN tmFormula maybeFocusArrow term
    {let (_11, pat0, _100, e00, focus0, e1) = ((), $2, (), $4, $5, $6) in
let pb =
  let e = e1 in
  let focus = focus0 in
  let e0 = e00 in
  let _10 = _100 in
  let pat = pat0 in
  let _1 = _11 in
  let when_opt =
    let e = e0 in
    let _1 = _10 in
                             ( Some e )
  in
        (
        let pat = match pat with
          | [p] -> p
          | ps -> mk_pattern (PatOr ps) (rhs2 parseState 1 2)
        in
        (focus, (pat, when_opt, e))
      )
in
                             ( pb )}

tmIff:
  tmIff IFF tmIff
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("<==>", [e1; e2])) (rhs2 parseState 1 3) Formula )}
| tmIff IMPLIES tmIff
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("==>", [e1; e2])) (rhs2 parseState 1 3) Formula )}
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
  tmFormula DISJUNCTION tmFormula
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("\\/", [e1;e2])) (rhs2 parseState 1 3) Formula )}
| tmFormula CONJUNCTION tmFormula
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("/\\", [e1;e2])) (rhs2 parseState 1 3) Formula )}
| separated_nonempty_list_COMMA_tmEq_
    {let el = $1 in
      (
        match el with
          | [x] -> x
          | components -> mkTuple components (rhs2 parseState 1 1)
      )}

tmEq:
  tmEq BACKTICK lid BACKTICK tmEq
    {let (e1, _2, id, _4, e2) = ($1, (), $3, (), $5) in
      ( mkApp (mk_term (Var id) (rhs2 parseState 2 4) Un) [ e1, Nothing; e2, Nothing ] (rhs2 parseState 1 5) )}
| tmEq EQUALS tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("=", [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq COLON_EQUALS tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op(":=", [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq PIPE_RIGHT tmEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("|>", [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0a tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0b tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0c tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX0d tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX1 tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmEq OPINFIX2 tmEq
    {let (e1, op0, e2) = ($1, $2, $3) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
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
            | _ -> raise (Error("Missing binder for the first component of a dependent tuple", rhs2 parseState 1 2)) in
        let dom = mkRefinedBinder x t true f (rhs2 parseState 1 2) None in
        let tail = e2 in
        let dom, res = match tail.tm with
            | Sum(dom', res) -> dom::dom', res
            | _ -> [dom], tail in
        mk_term (Sum(dom, res)) (rhs2 parseState 1 6) Type
      )}
| tmNoEq MINUS tmNoEq
    {let (e1, _2, e2) = ($1, (), $3) in
      ( mk_term (Op("-", [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmNoEq OPINFIX3 tmNoEq
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| tmNoEq OPINFIX4 tmNoEq
    {let (e1, op, e2) = ($1, $2, $3) in
      ( mk_term (Op(op, [e1; e2])) (rhs2 parseState 1 3) Un)}
| MINUS tmNoEq
    {let (_1, e) = ((), $2) in
      ( mk_uminus e (rhs2 parseState 1 3) Expr )}
| refinementTerm
    {let e = $1 in
      ( e )}

refinementTerm:
  ident COLON appTerm refineOpt
    {let (id, _2, e, phi_opt) = ($1, (), $3, $4) in
      (
        let t = match phi_opt with
          | None -> NamedTyp(id, e)
          | Some phi -> Refine(mk_binder (Annotated(id, e)) (rhs2 parseState 1 3) Type None, phi)
        in mk_term t (rhs2 parseState 1 4) Type
      )}
| LBRACE recordExp RBRACE
    {let (_1, e, _3) = ((), $2, ()) in
                              ( e )}
| unaryTerm
    {let e = $1 in
                ( e )}

refineOpt:
  option___anonymous_5_
    {let phi_opt = $1 in
                                                    (phi_opt)}

recordExp:
  separated_trailing_list_SEMICOLON_simpleDef_
    {let record_fields = $1 in
      ( mk_term (Record (None, record_fields)) (rhs2 parseState 1 2) Expr )}
| appTerm WITH simpleDef separated_trailing_tail_SEMICOLON_simpleDef_
    {let (e, _2, first_field, record_fields) = ($1, (), $3, $4) in
      ( mk_term (Record (Some e, first_field::record_fields)) (rhs2 parseState 1 2) Expr )}

simpleDef:
  lid EQUALS simpleTerm
    {let (x0, _20, y0) = ($1, (), $3) in
let e =
  let y = y0 in
  let _2 = _20 in
  let x = x0 in
      ( (x, y) )
in
                                              ( e )}

unaryTerm:
  TILDE atomicTerm
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(op, [e])) (rhs2 parseState 1 3) Formula )}
| appTerm
    {let e = $1 in
              ( e )}

appTerm:
  indexingTerm list_pair_maybeHash_indexingTerm__
    {let (head, args) = ($1, $2) in
      ( mkApp head (map (fun (x,y) -> (y,x)) args) (rhs2 parseState 1 2) )}

indexingTerm:
  atomicTerm DOT_LPAREN term RPAREN
    {let (e1, _2, e2, _4) = ($1, (), $3, ()) in
      ( mk_term (Op(".()", [ e1; e2 ])) (rhs2 parseState 1 3) Expr )}
| atomicTerm DOT_LBRACK term RBRACK
    {let (e1, _2, e2, _4) = ($1, (), $3, ()) in
      ( mk_term (Op(".[]", [ e1; e2 ])) (rhs2 parseState 1 3) Expr )}
| atomicTerm
    {let e = $1 in
      ( e )}

atomicTerm:
  UNDERSCORE
    {let _1 = () in
               ( mk_term Wild (rhs parseState 1) Un )}
| ASSERT
    {let _1 = () in
             ( mk_term (Var assert_lid) (rhs parseState 1) Expr )}
| tvar
    {let tv = $1 in
                ( mk_term (Tvar tv) (rhs parseState 1) Type )}
| constant
    {let c = $1 in
               ( mk_term (Const c) (rhs parseState 1) Expr )}
| L_TRUE
    {let _1 = () in
             ( mk_term (Name (lid_of_path ["True"] (rhs parseState 1))) (rhs parseState 1) Type )}
| L_FALSE
    {let _1 = () in
              ( mk_term (Name (lid_of_path ["False"] (rhs parseState 1))) (rhs parseState 1) Type )}
| OPPREFIX atomicTerm
    {let (op, e) = ($1, $2) in
      ( mk_term (Op(op, [e])) (rhs2 parseState 1 3) Expr )}
| LPAREN OPPREFIX RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX3 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX4 RPAREN
    {let (_1, op0, _3) = ((), $2, ()) in
let op =
  let op = op0 in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LPAREN OPINFIX0a RPAREN
    {let (_1, op00, _3) = ((), $2, ()) in
let op =
  let op0 = op00 in
  let op =
    let op = op0 in
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
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
         ( op )
  in
       ( op )
in
      ( mk_term (Op(op, [])) (rhs2 parseState 1 3) Un )}
| LENS_PAREN_LEFT tmEq COMMA separated_nonempty_list_COMMA_tmEq_ LENS_PAREN_RIGHT
    {let (_1, e0, _3, el, _5) = ((), $2, (), $4, ()) in
      ( mkDTuple (e0::el) (rhs2 parseState 1 1) )}
| projectionLHS list___anonymous_6_
    {let (e, field_projs) = ($1, $2) in
      ( fold_left (fun e lid -> mk_term (Project(e, lid)) (rhs2 parseState 1 2) Expr ) e field_projs )}
| BEGIN term END
    {let (_1, e, _3) = ((), $2, ()) in
      ( e )}

projectionLHS:
  eitherQname option___anonymous_7_
    {let (id, targs_opt) = ($1, $2) in
      (
        let t = if is_name id then Name id else Var id in
        let e = mk_term t (rhs parseState 1) Un in
        match targs_opt with
        | None -> e
        | Some targs -> mkFsTypApp e targs (rhs2 parseState 1 4)
      )}
| LPAREN term option_pair_hasSort_simpleTerm__ RPAREN
    {let (_1, e, sort_opt, _4) = ((), $2, $3, ()) in
      (
        let e1 = match sort_opt with
          | None -> e
          | Some (level, t) -> mk_term (Ascribed(e,{t with level=level})) (rhs2 parseState 1 4) level
        in mk_term (Paren e1) (rhs2 parseState 1 4) (e.level)
      )}
| LBRACK_BAR separated_trailing_list_SEMICOLON_noSeqTerm_ BAR_RBRACK
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
| LBRACK separated_trailing_list_SEMICOLON_noSeqTerm_ RBRACK
    {let (_1, l0, _3) = ((), $2, ()) in
let es =
  let l = l0 in
                                                      ( l )
in
      ( mkConsList (rhs2 parseState 1 3) es )}
| PERCENT_LBRACK separated_trailing_list_SEMICOLON_noSeqTerm_ RBRACK
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

hasSort:
  SUBTYPE
    {let _1 = () in
            ( Expr )}
| SUBKIND
    {let _1 = () in
            ( Type )}

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

separated_trailing_list_SEMICOLON_noSeqTerm_:
  
    {    ( [] )}
| noSeqTerm separated_trailing_tail_SEMICOLON_noSeqTerm_
    {let (x, l) = ($1, $2) in
                                         ( x::l )}

separated_trailing_list_SEMICOLON_simpleDef_:
  
    {    ( [] )}
| simpleDef separated_trailing_tail_SEMICOLON_simpleDef_
    {let (x, l) = ($1, $2) in
                                         ( x::l )}

separated_trailing_tail_SEMICOLON_noSeqTerm_:
  
    {let _1 =
      ( None )
in
                 ( [] )}
| SEMICOLON
    {let x0 = () in
let _1 =
  let x = x0 in
      ( Some x )
in
                 ( [] )}
| SEMICOLON noSeqTerm separated_trailing_tail_SEMICOLON_noSeqTerm_
    {let (_1, x, l) = ((), $2, $3) in
                                               ( x::l )}

separated_trailing_tail_SEMICOLON_simpleDef_:
  
    {let _1 =
      ( None )
in
                 ( [] )}
| SEMICOLON
    {let x0 = () in
let _1 =
  let x = x0 in
      ( Some x )
in
                 ( [] )}
| SEMICOLON simpleDef separated_trailing_tail_SEMICOLON_simpleDef_
    {let (_1, x, l) = ((), $2, $3) in
                                               ( x::l )}

%%




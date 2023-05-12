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
%token MUT FN INVARIANT WHILE REF PARALLEL REWRITE

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
      PulseSugar.mk_decl lid (List.flatten bs) ascription body (rr $loc)
    }
    
pulseMultiBinder:
  | LPAREN qual_ids=nonempty_list(q=option(HASH) id=lidentOrUnderscore { (q, id) }) COLON t=appTerm RPAREN
    { List.map (fun (q, id) -> (as_aqual q, id, t)) qual_ids }
  | q=option(HASH) id=lidentOrUnderscore
    { [(as_aqual q, id, mk_term Wild (rr ($loc(id))) Un)] }

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
        PulseSugar.mk_comp ST t i r t2 (rr $loc)
    }


pulseStmtNoSeq:
  | OPEN i=quident
    { PulseSugar.mk_open i }
  | tm=appTerm
    { PulseSugar.mk_expr tm }
  | i=lident COLON_EQUALS a=noSeqTerm
    { PulseSugar.mk_assignment i a }
  | LET q=option(mutOrRefQualifier) i=lident typOpt=option(appTerm) EQUALS tm=noSeqTerm
    { PulseSugar.mk_let_binding q i typOpt (Some tm) }
  | LBRACE s=pulseStmt RBRACE
    { PulseSugar.mk_block s }
  | IF tm=appTermNoRecordExp vp=option(returnsVprop) LBRACE th=pulseStmt RBRACE e=option(elseBlock)
    { PulseSugar.mk_if tm vp th e }
  | MATCH tm=appTermNoRecordExp c=option(returnsAnnot) LBRACE brs=list(pulseMatchBranch) RBRACE
    { PulseSugar.mk_match tm c brs }
  | WHILE LPAREN tm=pulseStmt RPAREN INVARIANT i=lident DOT v=pulseVprop LBRACE body=pulseStmt RBRACE
    { PulseSugar.mk_while tm i v body }
  | INTRO p=pulseVprop WITH ws=nonempty_list(indexingTerm)
    { PulseSugar.mk_intro p ws }
  | PARALLEL REQUIRES p1=pulseVprop AND p2=pulseVprop
             ENSURES q1=pulseVprop AND q2=pulseVprop
             LBRACE b1=pulseStmt RBRACE
             LBRACE b2=pulseStmt RBRACE
    { PulseSugar.mk_par p1 p2 q1 q2 b1 b2 }
  | REWRITE p1=pulseVprop AS p2=pulseVprop
    { PulseSugar.mk_rewrite p1 p2 }

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
    { PulseSugar.mk_stmt s (rr $loc) }
  | s1=pulseStmtNoSeq SEMICOLON s2=option(pulseStmt)
    {
      let s1 = PulseSugar.mk_stmt s1 (rr ($loc(s1))) in
      match s2 with
      | None -> s1
      | Some s2 -> PulseSugar.mk_stmt (PulseSugar.mk_sequence s1 s2) (rr ($loc(s2)))
    }

elseBlock:
  | ELSE LBRACE p=pulseStmt RBRACE
    { p }

mutOrRefQualifier:
  | MUT { MUT }
  | REF { REF }

pulseVprop:
  | t=appTermNoRecordExp
    { PulseSugar.VPropTerm t }
  | EXISTS bs=nonempty_list(pulseMultiBinder) DOT body=pulseVprop
    { PulseSugar.mk_vprop_exists (List.flatten bs) body }

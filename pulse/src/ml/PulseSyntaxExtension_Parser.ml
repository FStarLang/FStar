open Lexing
open FStar_Pervasives_Native
open FStar_Pervasives
open FStarC_Range
open FStarC_Parser_ParseIt
module FP = FStarC_Parser_Parse
module PP = Pulse_FStar_Parser
module S = FStarC_Sedlexing

let rewrite_token (tok:FP.token)
  : PP.token
  = match tok with
    | IDENT "mut" -> PP.MUT
    | IDENT "invariant" -> PP.INVARIANT
    | IDENT "predicate" -> PP.PREDICATE
    | IDENT "while" -> PP.WHILE
    | IDENT "fn" -> PP.FN
    | IDENT "divergent" -> PP.DIVERGENT
    | IDENT "each" -> PP.EACH
    | IDENT "rewrite" -> PP.REWRITE
    | IDENT "fold" -> PP.FOLD
    | IDENT "atomic" -> PP.ATOMIC
    | IDENT "ghost" -> PP.GHOST
    | IDENT "unobservable" -> PP.UNOBSERVABLE
    | IDENT "opens" -> PP.OPENS
    | IDENT "show_proof_state" -> PP.SHOW_PROOF_STATE
    | IDENT "norewrite" -> PP.NOREWRITE
    | IDENT "preserves" -> PP.PRESERVES
    | IDENT "goto" -> PP.GOTO
    | IDENT "label" -> PP.LABEL
    | IDENT "return" -> PP.RETURN
    | IDENT "continue" -> PP.CONTINUE
    | IDENT "break" -> PP.BREAK
    | IDENT "defer" -> PP.DEFER
    (* the rest are just copied from FStarC_Parser_Parse *)
    | IDENT s -> PP.IDENT s
    | AMP -> PP.AMP
    | AND -> PP.AND
    | AND_OP s -> PP.AND_OP s
    | AS -> PP.AS
    | ASSERT -> PP.ASSERT
    | ASSUME -> PP.ASSUME
    | BACKTICK -> PP.BACKTICK
    | BACKTICK_AT -> PP.BACKTICK_AT
    | BACKTICK_HASH -> PP.BACKTICK_HASH
    | BACKTICK_PERC -> PP.BACKTICK_PERC
    | BANG_LBRACE -> PP.BANG_LBRACE
    | BAR -> PP.BAR
    | BAR_RBRACE -> PP.BAR_RBRACE
    | BAR_RBRACK -> PP.BAR_RBRACK
    | BEGIN -> PP.BEGIN
    | BLOB s -> PP.BLOB s
    | BY -> PP.BY
    | CALC -> PP.CALC
    | CHAR c -> PP.CHAR c
    | CLASS -> PP.CLASS
    | COLON -> PP.COLON
    | COLON_COLON -> PP.COLON_COLON
    | COLON_EQUALS -> PP.COLON_EQUALS
    | COMMA -> PP.COMMA
    | CONJUNCTION -> PP.CONJUNCTION
    | DECREASES -> PP.DECREASES
    | DISJUNCTION -> PP.DISJUNCTION
    | DOLLAR -> PP.DOLLAR 
    | DOT -> PP.DOT 
    | DOT_DOT -> PP.DOT_DOT
    | DOT_LBRACK -> PP.DOT_LBRACK 
    | DOT_LBRACK_BAR -> PP.DOT_LBRACK_BAR 
    | DOT_LENS_PAREN_LEFT -> PP.DOT_LENS_PAREN_LEFT 
    | DOT_LPAREN -> PP.DOT_LPAREN 
    | EFFECT -> PP.EFFECT 
    | ELIM -> PP.ELIM 
    | ELSE -> PP.ELSE 
    | END -> PP.END 
    | ENSURES -> PP.ENSURES 
    | EOF -> PP.EOF 
    | EQUALS -> PP.EQUALS 
    | EQUALTYPE -> PP.EQUALTYPE 
    | EXCEPTION -> PP.EXCEPTION 
    | EXISTS -> PP.EXISTS
    | EXISTS_OP s -> PP.EXISTS_OP s
    | FALSE -> PP.FALSE 
    | FORALL -> PP.FORALL
    | FORALL_OP s -> PP.FORALL_OP s
    | FRIEND -> PP.FRIEND 
    | FUN -> PP.FUN 
    | FUNCTION -> PP.FUNCTION 
    | HASH -> PP.HASH 
    | IF -> PP.IF 
    | IFF -> PP.IFF 
    | IF_OP s -> PP.IF_OP s
    | IMPLIES -> PP.IMPLIES 
    | IN -> PP.IN 
    | INCLUDE -> PP.INCLUDE 
    | INLINE -> PP.INLINE 
    | INLINE_FOR_EXTRACTION -> PP.INLINE_FOR_EXTRACTION 
    | INSTANCE -> PP.INSTANCE 
    | INT s -> PP.INT s
    | INT16 s -> PP.INT16 s
    | INT32 s -> PP.INT32 s
    | INT64 s -> PP.INT64 s
    | INT8 s -> PP.INT8 s
    | INTRO -> PP.INTRO 
    | IRREDUCIBLE -> PP.IRREDUCIBLE 
    | LARROW -> PP.LARROW 
    | LBRACE -> PP.LBRACE 
    | LBRACE_BAR -> PP.LBRACE_BAR 
    | LBRACE_COLON_PATTERN -> PP.LBRACE_COLON_PATTERN 
    | LBRACE_COLON_WELL_FOUNDED -> PP.LBRACE_COLON_WELL_FOUNDED 
    | LBRACK -> PP.LBRACK 
    | LBRACK_AT -> PP.LBRACK_AT 
    | LBRACK_AT_AT -> PP.LBRACK_AT_AT 
    | LBRACK_AT_AT_AT -> PP.LBRACK_AT_AT_AT 
    | LBRACK_BAR -> PP.LBRACK_BAR 
    | LENS_PAREN_LEFT -> PP.LENS_PAREN_LEFT 
    | LENS_PAREN_RIGHT -> PP.LENS_PAREN_RIGHT 
    | LET -> PP.LET
    | LET_OP s -> PP.LET_OP s
    | LOGIC -> PP.LOGIC 
    | LONG_LEFT_ARROW -> PP.LONG_LEFT_ARROW 
    | LPAREN -> PP.LPAREN 
    | LPAREN_RPAREN -> PP.LPAREN_RPAREN 
    | MATCH -> PP.MATCH 
    | MATCH_OP s -> PP.MATCH_OP s
    | MINUS -> PP.MINUS 
    | MODULE -> PP.MODULE 
    | NAME s -> PP.NAME s
    | NEW -> PP.NEW 
    | NEW_EFFECT -> PP.NEW_EFFECT 
    | NOEQUALITY -> PP.NOEQUALITY 
    | NOEXTRACT -> PP.NOEXTRACT 
    | OF -> PP.OF 
    | OPAQUE -> PP.OPAQUE 
    | OPEN -> PP.OPEN 
    | OPINFIX0a s -> PP.OPINFIX0a s 
    | OPINFIX0b s -> PP.OPINFIX0b s 
    | OPINFIX0c s -> PP.OPINFIX0c s 
    | OPINFIX0d s -> PP.OPINFIX0d s 
    | OPINFIX1 s -> PP.OPINFIX1 s 
    | OPINFIX2 s -> PP.OPINFIX2 s 
    | OPINFIX3L s -> PP.OPINFIX3L s
    | OPINFIX3R s -> PP.OPINFIX3R s
    | OPINFIX4 s -> PP.OPINFIX4 s 
    | OPPREFIX s -> PP.OPPREFIX s 
    | OP_MIXFIX_ACCESS s -> PP.OP_MIXFIX_ACCESS s 
    | OP_MIXFIX_ASSIGNMENT s -> PP.OP_MIXFIX_ASSIGNMENT s 
    | PERCENT_LBRACK -> PP.PERCENT_LBRACK 
    | PIPE_LEFT -> PP.PIPE_LEFT
    | PIPE_RIGHT -> PP.PIPE_RIGHT 
    | PRAGMA_POP_OPTIONS -> PP.PRAGMA_POP_OPTIONS 
    | PRAGMA_PRINT_EFFECTS_GRAPH -> PP.PRAGMA_PRINT_EFFECTS_GRAPH 
    | PRAGMA_PUSH_OPTIONS -> PP.PRAGMA_PUSH_OPTIONS 
    | PRAGMA_RESET_OPTIONS -> PP.PRAGMA_RESET_OPTIONS 
    | PRAGMA_RESTART_SOLVER -> PP.PRAGMA_RESTART_SOLVER 
    | PRAGMA_SET_OPTIONS -> PP.PRAGMA_SET_OPTIONS 
    | PRAGMA_SHOW_OPTIONS -> PP.PRAGMA_SHOW_OPTIONS
    | PRAGMA_CHECK -> PP.PRAGMA_CHECK
    | PRAGMA_EVAL -> PP.PRAGMA_EVAL
    | PRIVATE -> PP.PRIVATE 
    | QMARK -> PP.QMARK 
    | QMARK_DOT -> PP.QMARK_DOT 
    | QUOTE -> PP.QUOTE 
    | RANGE_OF -> PP.RANGE_OF 
    | RARROW -> PP.RARROW 
    | RBRACE -> PP.RBRACE 
    | RBRACK -> PP.RBRACK 
    | REAL s -> PP.REAL s 
    | REC -> PP.REC 
    | REFLECTABLE -> PP.REFLECTABLE 
    | REIFIABLE -> PP.REIFIABLE 
    | REIFY -> PP.REIFY 
    | REQUIRES -> PP.REQUIRES 
    | RETURNS -> PP.RETURNS 
    | RETURNS_EQ -> PP.RETURNS_EQ 
    | RPAREN -> PP.RPAREN 
    | SEQ_BANG_LBRACK -> PP.SEQ_BANG_LBRACK
    | SEMICOLON -> PP.SEMICOLON 
    | SEMICOLON_OP s -> PP.SEMICOLON_OP s
    | SET_RANGE_OF -> PP.SET_RANGE_OF 
    | SIZET s -> PP.SIZET s 
    | SPLICE -> PP.SPLICE 
    | SPLICET -> PP.SPLICET 
    | SQUIGGLY_RARROW -> PP.SQUIGGLY_RARROW 
    | STRING s -> PP.STRING s 
    | SUBKIND -> PP.SUBKIND 
    | SUBTYPE -> PP.SUBTYPE 
    | SUB_EFFECT -> PP.SUB_EFFECT 
    | SYNTH -> PP.SYNTH 
    | THEN -> PP.THEN 
    | TILDE s -> PP.TILDE s 
    | TOTAL -> PP.TOTAL 
    | TRUE -> PP.TRUE 
    | TRY -> PP.TRY 
    | TYPE -> PP.TYPE 
    | UINT16 s -> PP.UINT16 s 
    | UINT32 s -> PP.UINT32 s 
    | UINT64 s -> PP.UINT64 s 
    | UINT8 s -> PP.UINT8 s 
    | UNDERSCORE -> PP.UNDERSCORE 
    | UNFOLD -> PP.UNFOLD 
    | UNFOLDABLE -> PP.UNFOLDABLE 
    | UNIV_HASH -> PP.UNIV_HASH 
    | UNOPTEQUALITY -> PP.UNOPTEQUALITY
    | USE_LANG_BLOB s -> PP.USE_LANG_BLOB s
    | VAL -> PP.VAL 
    | WHEN -> PP.WHEN 
    | WITH -> PP.WITH 

let wrap_lexer lexbuf () =
  let tok = FStarC_Parser_LexFStar.token lexbuf in
  let rt = rewrite_token tok in
  rt, lexbuf.start_p, lexbuf.cur_p

let lexbuf_and_lexer (s:string) (r:range) = 
  let lexbuf =
    S.create s
             (file_of_range r)
             (Z.to_int (line_of_pos (start_of_range r)))
             (Z.to_int (col_of_pos (start_of_range r)))
  in
  lexbuf, wrap_lexer lexbuf
  

let parse_decl_menhir (s:string) (r:range) =
  let fn = file_of_range r in
  let lexbuf, lexer = lexbuf_and_lexer s r in
  try
    let d = MenhirLib.Convert.Simplified.traditional2revised PP.pulseDeclEOF lexer in
    Inl d
  with
  | e ->
    let pos = FStarC_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
    let r = FStarC_Range.mk_range fn pos pos in
    Inr (Some (FStar_Errors_Msg.mkmsg "Syntax error", r))

 
let parse_peek_id_menhir (s:string) (r:range) : (string, FStar_Pprint.document list * range) either =
  (* print_string ("About to parse <" ^ s ^ ">"); *)
  let fn = file_of_range r in
  let lexbuf, lexer = lexbuf_and_lexer s r in
  try
    let lid = MenhirLib.Convert.Simplified.traditional2revised PP.peekFnId lexer in
    Inl lid
  with
  | e ->
    let pos = FStarC_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
    let r = FStarC_Range.mk_range fn pos pos in
    Inr (FStar_Errors_Msg.mkmsg "Syntax error", r)


let parse_lang_menhir (s:string) (r:range) =
  let fn = file_of_range r in
  let lexbuf, lexer = lexbuf_and_lexer s r in
  let range_of_either (d: (PulseSyntaxExtension_Sugar.decl, FStarC_Parser_AST.decl) either) =
      match d with 
      | Inl d -> PulseSyntaxExtension_Sugar.range_of_decl d
      | Inr f -> f.drange
  in
  try
    let ds, err = FStarC_Parser_ParseIt.parse_incremental_decls fn s lexbuf lexer range_of_either PP.iLangDeclOrEOF in
    Inl (ds, err)
  with
  | e ->
    let pos = FStarC_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
    let r = FStarC_Range.mk_range fn pos pos in
    Inr (Some (FStar_Errors_Msg.mkmsg "#lang-pulse: Syntax error", r))


(* The new parser (PulseSyntaxExtension.Grammar), selected like the F*
   one: it is the default, and --ext parser=menhir selects Menhir. With
   --ext parser=compare, both parsers are run, differences are reported
   on stderr, and the result of the Menhir parser is used. *)
let err_str (msg, r) =
  Printf.sprintf "%s: %s" (FStarC_Range_Ops.string_of_range r) (FStarC_Errors_Msg.rendermsg msg)

let report_err fname what e1 e2 =
  match e1, e2 with
  | None, None -> ()
  | Some e1, Some e2 ->
    if err_str e1 <> err_str e2 then
      Printf.eprintf "PARSER-COMPARE %s: %s errors differ\n  menhir: %s\n  new:    %s\n%!" fname what (err_str e1) (err_str e2)
  | Some e1, None -> Printf.eprintf "PARSER-COMPARE %s: %s only menhir failed: %s\n%!" fname what (err_str e1)
  | None, Some e2 -> Printf.eprintf "PARSER-COMPARE %s: %s only new failed: %s\n%!" fname what (err_str e2)

let run_compare fname what menhir_fn new_fn compare =
  let g0 = FStarC_GenSym.get_gensym_state () in
  let r_old = menhir_fn () in
  let g1 = FStarC_GenSym.get_gensym_state () in
  FStarC_GenSym.set_gensym_state g0;
  (try
     let r_new = new_fn () in
     compare r_old r_new
   with e ->
     Printf.eprintf "PARSER-COMPARE %s: %s new parser raised %s\n%!" fname what (Printexc.to_string e));
  FStarC_GenSym.set_gensym_state g1;
  r_old

let parse_decl (s:string) (r:range) =
  match FStarC_Parser_ParseIt.parser_mode () with
  | "new" -> PulseSyntaxExtension_Grammar.parse_decl s r
  | "compare" ->
    let fname = file_of_range r in
    run_compare fname "pulse decl" (fun () -> parse_decl_menhir s r)
      (fun () -> PulseSyntaxExtension_Grammar.parse_decl s r)
      (fun r1 r2 ->
        match r1, r2 with
        | Inl d1, Inl d2 -> FStarC_Parser_ParseIt.report_diff fname "pulse decls" d1 d2
        | Inr e1, Inr e2 -> report_err fname "pulse decl" e1 e2
        | Inr e1, _ -> report_err fname "pulse decl" e1 None
        | _, Inr e2 -> report_err fname "pulse decl" None e2)
  | _ -> parse_decl_menhir s r

let parse_peek_id (s:string) (r:range) : (string, FStar_Pprint.document list * range) either =
  match FStarC_Parser_ParseIt.parser_mode () with
  | "new" -> PulseSyntaxExtension_Grammar.parse_peek_id s r
  | "compare" ->
    let fname = file_of_range r in
    run_compare fname "pulse peek id" (fun () -> parse_peek_id_menhir s r)
      (fun () -> PulseSyntaxExtension_Grammar.parse_peek_id s r)
      (fun r1 r2 ->
        match r1, r2 with
        | Inl d1, Inl d2 -> FStarC_Parser_ParseIt.report_diff fname "pulse peek ids" d1 d2
        | Inr e1, Inr e2 -> report_err fname "pulse peek id" (Some e1) (Some e2)
        | Inr e1, _ -> report_err fname "pulse peek id" (Some e1) None
        | _, Inr e2 -> report_err fname "pulse peek id" None (Some e2))
  | _ -> parse_peek_id_menhir s r

let parse_lang_new (s:string) (r:range) =
  match PulseSyntaxExtension_Grammar.parse_lang s r with
  | Inl (ds, err, comments) -> Inl (ds, err), comments
  | Inr e -> Inr e, []

let parse_lang (s:string) (r:range) =
  match FStarC_Parser_ParseIt.parser_mode () with
  | "new" ->
    let res, comments = parse_lang_new s r in
    (* Like the Menhir lexer, leave the comments in the buffer of the F* parser *)
    List.iter FStarC_Parser_Util.add_comment (List.rev comments);
    res
  | "compare" ->
    let fname = file_of_range r in
    let as_err = function None -> None | Some (_, msg, r) -> Some (msg, r) in
    let saved = FStarC_Parser_Util.flush_comments () in
    let c_old = ref [] in
    let res =
      run_compare fname "pulse lang"
        (fun () ->
          let res = parse_lang_menhir s r in
          c_old := FStarC_Parser_Util.flush_comments ();
          res)
        (fun () -> parse_lang_new s r)
        (fun r1 (r2, c_new) ->
          FStarC_Parser_ParseIt.report_diff fname "pulse comments" !c_old c_new;
          match r1, r2 with
          | Inl (d1, e1), Inl (d2, e2) ->
            FStarC_Parser_ParseIt.report_diff fname "pulse decls" d1 d2;
            report_err fname "pulse lang" (as_err e1) (as_err e2)
          | Inr e1, Inr e2 -> report_err fname "pulse lang" e1 e2
          | Inr e1, _ -> report_err fname "pulse lang" e1 None
          | _, Inr e2 -> report_err fname "pulse lang" None e2)
    in
    FStarC_Parser_Util.comments := !c_old @ saved;
    res
  | _ -> parse_lang_menhir s r

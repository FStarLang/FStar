open Lexing
open FStar_Pervasives_Native
open FStar_Pervasives
open FStar_Compiler_Range
open FStar_Parser_ParseIt
module FP = FStar_Parser_Parse
module PP = Pulse_FStar_Parser
module S = FStar_Sedlexing

let rewrite_token (tok:FP.token)
  : PP.token
  = match tok with
    | IDENT "mut" -> PP.MUT
    | IDENT "invariant" -> PP.INVARIANT
    | IDENT "while" -> PP.WHILE
    | IDENT "fn" -> PP.FN
    | IDENT "parallel" -> PP.PARALLEL
    | IDENT "each" -> PP.EACH
    | IDENT "rewrite" -> PP.REWRITE
    | IDENT "fold" -> PP.FOLD
    | IDENT "atomic" -> PP.ATOMIC
    | IDENT "ghost" -> PP.GHOST
    (* the rest are just copied from FStar_Parser_Parse *)
    | IDENT s -> PP.IDENT s
    | AMP -> PP.AMP
    | AND -> PP.AND
    | AND_OP s -> PP.AND_OP s
    | AS -> PP.AS
    | ASSERT -> PP.ASSERT
    | ASSUME -> PP.ASSUME
    | ATTRIBUTES -> PP.ATTRIBUTES
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
    | DEFAULT -> PP.DEFAULT
    | DISJUNCTION -> PP.DISJUNCTION
    | DOLLAR -> PP.DOLLAR 
    | DOT -> PP.DOT 
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
    | FALSE -> PP.FALSE 
    | FORALL -> PP.FORALL 
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
    | LAYERED_EFFECT -> PP.LAYERED_EFFECT 
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
    | LET b -> PP.LET b
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
    | OPINFIX3 s -> PP.OPINFIX3 s 
    | OPINFIX4 s -> PP.OPINFIX4 s 
    | OPPREFIX s -> PP.OPPREFIX s 
    | OP_MIXFIX_ACCESS s -> PP.OP_MIXFIX_ACCESS s 
    | OP_MIXFIX_ASSIGNMENT s -> PP.OP_MIXFIX_ASSIGNMENT s 
    | PERCENT_LBRACK -> PP.PERCENT_LBRACK 
    | PIPE_RIGHT -> PP.PIPE_RIGHT 
    | POLYMONADIC_BIND -> PP.POLYMONADIC_BIND 
    | POLYMONADIC_SUBCOMP -> PP.POLYMONADIC_SUBCOMP 
    | PRAGMA_POP_OPTIONS -> PP.PRAGMA_POP_OPTIONS 
    | PRAGMA_PRINT_EFFECTS_GRAPH -> PP.PRAGMA_PRINT_EFFECTS_GRAPH 
    | PRAGMA_PUSH_OPTIONS -> PP.PRAGMA_PUSH_OPTIONS 
    | PRAGMA_RESET_OPTIONS -> PP.PRAGMA_RESET_OPTIONS 
    | PRAGMA_RESTART_SOLVER -> PP.PRAGMA_RESTART_SOLVER 
    | PRAGMA_SET_OPTIONS -> PP.PRAGMA_SET_OPTIONS 
    | PRIVATE -> PP.PRIVATE 
    | QMARK -> PP.QMARK 
    | QMARK_DOT -> PP.QMARK_DOT 
    | QUOTE -> PP.QUOTE 
    | RANGE s -> PP.RANGE s 
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
    | TVAR s -> PP.TVAR s 
    | TYPE -> PP.TYPE 
    | TYP_APP_GREATER -> PP.TYP_APP_GREATER 
    | TYP_APP_LESS -> PP.TYP_APP_LESS 
    | UINT16 s -> PP.UINT16 s 
    | UINT32 s -> PP.UINT32 s 
    | UINT64 s -> PP.UINT64 s 
    | UINT8 s -> PP.UINT8 s 
    | UNDERSCORE -> PP.UNDERSCORE 
    | UNFOLD -> PP.UNFOLD 
    | UNFOLDABLE -> PP.UNFOLDABLE 
    | UNIV_HASH -> PP.UNIV_HASH 
    | UNOPTEQUALITY -> PP.UNOPTEQUALITY 
    | VAL -> PP.VAL 
    | WHEN -> PP.WHEN 
    | WITH -> PP.WITH 

let wrap_lexer lexbuf () =
  let tok = FStar_Parser_LexFStar.token lexbuf in
  rewrite_token tok, lexbuf.start_p, lexbuf.cur_p

let lexbuf_and_lexer (s:string) (r:range) = 
  let lexbuf =
    S.create s
             (file_of_range r)
             (Z.to_int (line_of_pos (start_of_range r)))
             (Z.to_int (col_of_pos (start_of_range r)))
  in
  lexbuf, wrap_lexer lexbuf
  

let parse_decl (s:string) (r:range) =
  let fn = file_of_range r in
  let lexbuf, lexer = lexbuf_and_lexer s r in
  try
    let d = MenhirLib.Convert.Simplified.traditional2revised PP.pulseDecl lexer in
    Inl d
  with
  | e ->
    let pos = FStar_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
    let r = FStar_Compiler_Range.mk_range fn pos pos in
    Inr (Some ("Syntax error", r))

 
let parse_peek_id (s:string) (r:range) : (string, string * range) either =
  (* print_string ("About to parse <" ^ s ^ ">"); *)
  let fn = file_of_range r in
  let lexbuf, lexer = lexbuf_and_lexer s r in
  try
    let lid = MenhirLib.Convert.Simplified.traditional2revised PP.peekFnId lexer in
    Inl lid
  with
  | e ->
    let pos = FStar_Parser_Util.pos_of_lexpos (lexbuf.cur_p) in
    let r = FStar_Compiler_Range.mk_range fn pos pos in
    let msg = FStar_Compiler_Util.format3 
         "Failed to peek id, Syntax error @ %s\n%s\n%s\n"
          (FStar_Compiler_Range.string_of_range r)
          (Printexc.to_string e)
          (Printexc.get_backtrace()) in
    Inr (msg, r)


type token =
  | BYTEARRAY of (bytes)
  | STRING of (bytes)
  | IDENT of (string)
  | IDENT_LESS of (string)
  | NAME of (string)
  | TVAR of (string)
  | DIV_MOD_OP of (string)
  | TILDE of (string)
  | CUSTOM_OP of (string)
  | INT8 of (sbyte * bool)
  | INT16 of (int16 * bool)
  | INT32 of (int32 * bool)
  | INT32_DOT_DOT of (int32 * bool)
  | INT64 of (int64 * bool)
  | INT of (int32 * bool)
  | UINT8 of (byte)
  | UINT16 of (uint16)
  | UINT32 of (uint32)
  | UINT64 of (uint64)
  | UNATIVEINT of (uint64)
  | NATIVEINT of (int64)
  | IEEE32 of (single)
  | IEEE64 of (double)
  | CHAR of (char)
  | DECIMAL of (decimal)
  | BIGINT of (bytes)
  | BIGNUM of (bytes)
  | LET of (bool)
  | LQUOTE of (string * bool)
  | RQUOTE of (string * bool)
  | FORALL
  | EXISTS
  | ASSUME
  | QUERY
  | DEFINE
  | LOGIC
  | OPAQUE
  | PRAGMALIGHT
  | PRAGMA_SET_OPTIONS
  | PRAGMA_RESET_OPTIONS
  | BAR_BAR
  | LEQ
  | GEQ
  | LESS
  | LESSLESS
  | TYP_APP_LESS
  | TYP_APP_GREATER
  | LESSGREATER
  | SUBTYPE
  | SUBKIND
  | BANG
  | AND
  | AS
  | ASSERT
  | BEGIN
  | ELSE
  | END
  | DOT_DOT
  | EXCEPTION
  | FALSE
  | FOR
  | FUN
  | FUNCTION
  | IF
  | IN
  | FINALLY
  | RESERVED
  | MODULE
  | DEFAULT
  | LAZY
  | MATCH
  | OF
  | OPEN
  | OR
  | REC
  | THEN
  | TO
  | TRUE
  | TRY
  | TYPE
  | EFFECT
  | VAL
  | WHEN
  | WITH
  | HASH
  | AMP
  | AMP_AMP
  | QUOTE
  | LPAREN
  | RPAREN
  | LPAREN_RPAREN
  | STAR
  | COMMA
  | RARROW
  | IFF
  | IMPLIES
  | CONJUNCTION
  | DISJUNCTION
  | DOT
  | COLON
  | COLON_COLON
  | ATSIGN
  | HAT
  | COLON_EQUALS
  | SEMICOLON
  | SEMICOLON_SEMICOLON
  | EQUALS
  | EQUALS_EQUALS
  | PERCENT_LBRACK
  | LBRACK
  | LBRACK_BAR
  | LBRACE
  | BACKSLASH
  | BAR_RBRACK
  | UNDERSCORE
  | LENS_PAREN_LEFT
  | LENS_PAREN_RIGHT
  | BAR
  | RBRACK
  | RBRACE
  | MINUS
  | DOLLAR
  | PUBLIC
  | PRIVATE
  | LBRACE_COLON_PATTERN
  | PIPE_LEFT
  | PIPE_RIGHT
  | NEW_EFFECT
  | SUB_EFFECT
  | SQUIGGLY_RARROW
  | TOTAL
  | KIND
  | PRINT
  | REQUIRES
  | ENSURES
  | PLUS_OP
  | MINUS_OP
  | LEX_FAILURE of (string)
  | COMMENT
  | WHITESPACE
  | HASH_LINE
  | HASH_LIGHT
  | HASH_IF
  | HASH_ELSE
  | HASH_ENDIF
  | INACTIVECODE
  | LINE_COMMENT
  | STRING_TEXT
  | EOF

val inputFragment :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> inputFragment

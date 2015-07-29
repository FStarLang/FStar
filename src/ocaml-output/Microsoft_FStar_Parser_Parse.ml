
type token =
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
| LEX_FAILURE of string
| REQUIRES
| ENSURES
| EXTERN
| REFERENCE
| VOID
| PUBLIC
| PRINT
| PRIVATE
| INTERNAL
| LBRACE_COLON_PATTERN
| LBRACE_TILDE
| TILDE_RBRACE
| PIPE_LEFT
| PIPE_RIGHT
| STATIC
| MEMBER
| CLASS
| VIRTUAL
| ABSTRACT
| OVERRIDE
| OPAQUE
| DEFAULT
| CONSTRUCTOR
| INHERIT
| GREATER_RBRACK
| STRUCT
| SIG
| BAR
| RBRACK
| RBRACE
| MINUS
| DOLLAR
| LBRACE_LESS
| BAR_RBRACK
| GREATER_RBRACE
| UNDERSCORE
| SEMICOLON_SEMICOLON
| LARROW
| EQUALS
| PERCENT_LBRACK
| LBRACK
| LBRACK_BAR
| LBRACK_LESS
| LBRACE
| BACKSLASH
| QMARK
| QMARK_QMARK
| DOT
| COLON
| COLON_COLON
| ATSIGN
| HAT
| COLON_GREATER
| COLON_QMARK_GREATER
| COLON_QMARK
| COLON_EQUALS
| SEMICOLON
| GREATER_DOT
| GREATER_BAR_RBRACK
| LPAREN_STAR_RPAREN
| IFF
| IMPLIES
| CONJUNCTION
| DISJUNCTION
| WHEN
| WHILE
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
| RARROW2
| RRARROW
| OPEN
| OR
| PROP
| REC
| THEN
| TO
| TRUE
| TRY
| EFFECT
| TYPE
| KIND
| VAL
| INLINE
| INTERFACE
| INSTANCE
| LAZY
| MATCH
| METHOD
| MUTABLE
| NEW
| NEW_EFFECT
| OF
| EXCEPTION
| FALSE
| FOR
| FUN
| FUNCTION
| IF
| IN
| FINALLY
| DO_BANG
| AND
| AS
| ASSERT
| ASR
| BEGIN
| DO
| DONE
| DOWNTO
| ELSE
| ELIF
| END
| DOT_DOT
| BAR_BAR
| LEQ
| GEQ
| LESSLESS
| LESS
| GREATER
| LESSGREATER
| UPCAST
| DOWNCAST
| NULL
| RESERVED
| MODULE
| DELEGATE
| CONSTRAINT
| BASE
| SUB_EFFECT
| SUBTYPE
| SUBKIND
| FORALL
| EXISTS
| ASSUME
| QUERY
| DEFINE
| LOGIC
| PRAGMALIGHT
| PRAGMA_SET_OPTIONS
| PRAGMA_RESET_OPTIONS
| MONADLATTICE
| SQUIGGLY_RARROW
| TOTAL
| LET of bool
| INFIX_STAR_DIV_MOD_OP of string
| DIV_MOD_OP of string
| PREFIX_OP of string
| INFIX_BAR_OP of string
| INFIX_AT_HAT_OP of string
| INFIX_COMPARE_OP of string
| INFIX_STAR_STAR_OP of string
| LANG of string
| BASEKIND of string
| TVAR of string
| NAME of string
| IDENT_LESS of string
| IDENT of string
| STRING of Support.Prims.byte array
| INT32 of (Support.Prims.int32 * bool)
| INT of (string * bool)
| YIELD of bool

let is_COMMENT = (fun ( _discr_ ) -> (match (_discr_) with
| COMMENT -> begin
true
end
| _ -> begin
false
end))

let is_WHITESPACE = (fun ( _discr_ ) -> (match (_discr_) with
| WHITESPACE -> begin
true
end
| _ -> begin
false
end))

let is_HASH_LINE = (fun ( _discr_ ) -> (match (_discr_) with
| HASH_LINE -> begin
true
end
| _ -> begin
false
end))

let is_HASH_LIGHT = (fun ( _discr_ ) -> (match (_discr_) with
| HASH_LIGHT -> begin
true
end
| _ -> begin
false
end))

let is_HASH_IF = (fun ( _discr_ ) -> (match (_discr_) with
| HASH_IF -> begin
true
end
| _ -> begin
false
end))

let is_HASH_ELSE = (fun ( _discr_ ) -> (match (_discr_) with
| HASH_ELSE -> begin
true
end
| _ -> begin
false
end))

let is_HASH_ENDIF = (fun ( _discr_ ) -> (match (_discr_) with
| HASH_ENDIF -> begin
true
end
| _ -> begin
false
end))

let is_INACTIVECODE = (fun ( _discr_ ) -> (match (_discr_) with
| INACTIVECODE -> begin
true
end
| _ -> begin
false
end))

let is_LINE_COMMENT = (fun ( _discr_ ) -> (match (_discr_) with
| LINE_COMMENT -> begin
true
end
| _ -> begin
false
end))

let is_STRING_TEXT = (fun ( _discr_ ) -> (match (_discr_) with
| STRING_TEXT -> begin
true
end
| _ -> begin
false
end))

let is_EOF = (fun ( _discr_ ) -> (match (_discr_) with
| EOF -> begin
true
end
| _ -> begin
false
end))

let is_LEX_FAILURE = (fun ( _discr_ ) -> (match (_discr_) with
| LEX_FAILURE (_) -> begin
true
end
| _ -> begin
false
end))

let is_REQUIRES = (fun ( _discr_ ) -> (match (_discr_) with
| REQUIRES -> begin
true
end
| _ -> begin
false
end))

let is_ENSURES = (fun ( _discr_ ) -> (match (_discr_) with
| ENSURES -> begin
true
end
| _ -> begin
false
end))

let is_EXTERN = (fun ( _discr_ ) -> (match (_discr_) with
| EXTERN -> begin
true
end
| _ -> begin
false
end))

let is_REFERENCE = (fun ( _discr_ ) -> (match (_discr_) with
| REFERENCE -> begin
true
end
| _ -> begin
false
end))

let is_VOID = (fun ( _discr_ ) -> (match (_discr_) with
| VOID -> begin
true
end
| _ -> begin
false
end))

let is_PUBLIC = (fun ( _discr_ ) -> (match (_discr_) with
| PUBLIC -> begin
true
end
| _ -> begin
false
end))

let is_PRINT = (fun ( _discr_ ) -> (match (_discr_) with
| PRINT -> begin
true
end
| _ -> begin
false
end))

let is_PRIVATE = (fun ( _discr_ ) -> (match (_discr_) with
| PRIVATE -> begin
true
end
| _ -> begin
false
end))

let is_INTERNAL = (fun ( _discr_ ) -> (match (_discr_) with
| INTERNAL -> begin
true
end
| _ -> begin
false
end))

let is_LBRACE_COLON_PATTERN = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACE_COLON_PATTERN -> begin
true
end
| _ -> begin
false
end))

let is_LBRACE_TILDE = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACE_TILDE -> begin
true
end
| _ -> begin
false
end))

let is_TILDE_RBRACE = (fun ( _discr_ ) -> (match (_discr_) with
| TILDE_RBRACE -> begin
true
end
| _ -> begin
false
end))

let is_PIPE_LEFT = (fun ( _discr_ ) -> (match (_discr_) with
| PIPE_LEFT -> begin
true
end
| _ -> begin
false
end))

let is_PIPE_RIGHT = (fun ( _discr_ ) -> (match (_discr_) with
| PIPE_RIGHT -> begin
true
end
| _ -> begin
false
end))

let is_STATIC = (fun ( _discr_ ) -> (match (_discr_) with
| STATIC -> begin
true
end
| _ -> begin
false
end))

let is_MEMBER = (fun ( _discr_ ) -> (match (_discr_) with
| MEMBER -> begin
true
end
| _ -> begin
false
end))

let is_CLASS = (fun ( _discr_ ) -> (match (_discr_) with
| CLASS -> begin
true
end
| _ -> begin
false
end))

let is_VIRTUAL = (fun ( _discr_ ) -> (match (_discr_) with
| VIRTUAL -> begin
true
end
| _ -> begin
false
end))

let is_ABSTRACT = (fun ( _discr_ ) -> (match (_discr_) with
| ABSTRACT -> begin
true
end
| _ -> begin
false
end))

let is_OVERRIDE = (fun ( _discr_ ) -> (match (_discr_) with
| OVERRIDE -> begin
true
end
| _ -> begin
false
end))

let is_OPAQUE = (fun ( _discr_ ) -> (match (_discr_) with
| OPAQUE -> begin
true
end
| _ -> begin
false
end))

let is_DEFAULT = (fun ( _discr_ ) -> (match (_discr_) with
| DEFAULT -> begin
true
end
| _ -> begin
false
end))

let is_CONSTRUCTOR = (fun ( _discr_ ) -> (match (_discr_) with
| CONSTRUCTOR -> begin
true
end
| _ -> begin
false
end))

let is_INHERIT = (fun ( _discr_ ) -> (match (_discr_) with
| INHERIT -> begin
true
end
| _ -> begin
false
end))

let is_GREATER_RBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| GREATER_RBRACK -> begin
true
end
| _ -> begin
false
end))

let is_STRUCT = (fun ( _discr_ ) -> (match (_discr_) with
| STRUCT -> begin
true
end
| _ -> begin
false
end))

let is_SIG = (fun ( _discr_ ) -> (match (_discr_) with
| SIG -> begin
true
end
| _ -> begin
false
end))

let is_BAR = (fun ( _discr_ ) -> (match (_discr_) with
| BAR -> begin
true
end
| _ -> begin
false
end))

let is_RBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| RBRACK -> begin
true
end
| _ -> begin
false
end))

let is_RBRACE = (fun ( _discr_ ) -> (match (_discr_) with
| RBRACE -> begin
true
end
| _ -> begin
false
end))

let is_MINUS = (fun ( _discr_ ) -> (match (_discr_) with
| MINUS -> begin
true
end
| _ -> begin
false
end))

let is_DOLLAR = (fun ( _discr_ ) -> (match (_discr_) with
| DOLLAR -> begin
true
end
| _ -> begin
false
end))

let is_LBRACE_LESS = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACE_LESS -> begin
true
end
| _ -> begin
false
end))

let is_BAR_RBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| BAR_RBRACK -> begin
true
end
| _ -> begin
false
end))

let is_GREATER_RBRACE = (fun ( _discr_ ) -> (match (_discr_) with
| GREATER_RBRACE -> begin
true
end
| _ -> begin
false
end))

let is_UNDERSCORE = (fun ( _discr_ ) -> (match (_discr_) with
| UNDERSCORE -> begin
true
end
| _ -> begin
false
end))

let is_SEMICOLON_SEMICOLON = (fun ( _discr_ ) -> (match (_discr_) with
| SEMICOLON_SEMICOLON -> begin
true
end
| _ -> begin
false
end))

let is_LARROW = (fun ( _discr_ ) -> (match (_discr_) with
| LARROW -> begin
true
end
| _ -> begin
false
end))

let is_EQUALS = (fun ( _discr_ ) -> (match (_discr_) with
| EQUALS -> begin
true
end
| _ -> begin
false
end))

let is_PERCENT_LBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| PERCENT_LBRACK -> begin
true
end
| _ -> begin
false
end))

let is_LBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACK -> begin
true
end
| _ -> begin
false
end))

let is_LBRACK_BAR = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACK_BAR -> begin
true
end
| _ -> begin
false
end))

let is_LBRACK_LESS = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACK_LESS -> begin
true
end
| _ -> begin
false
end))

let is_LBRACE = (fun ( _discr_ ) -> (match (_discr_) with
| LBRACE -> begin
true
end
| _ -> begin
false
end))

let is_BACKSLASH = (fun ( _discr_ ) -> (match (_discr_) with
| BACKSLASH -> begin
true
end
| _ -> begin
false
end))

let is_QMARK = (fun ( _discr_ ) -> (match (_discr_) with
| QMARK -> begin
true
end
| _ -> begin
false
end))

let is_QMARK_QMARK = (fun ( _discr_ ) -> (match (_discr_) with
| QMARK_QMARK -> begin
true
end
| _ -> begin
false
end))

let is_DOT = (fun ( _discr_ ) -> (match (_discr_) with
| DOT -> begin
true
end
| _ -> begin
false
end))

let is_COLON = (fun ( _discr_ ) -> (match (_discr_) with
| COLON -> begin
true
end
| _ -> begin
false
end))

let is_COLON_COLON = (fun ( _discr_ ) -> (match (_discr_) with
| COLON_COLON -> begin
true
end
| _ -> begin
false
end))

let is_ATSIGN = (fun ( _discr_ ) -> (match (_discr_) with
| ATSIGN -> begin
true
end
| _ -> begin
false
end))

let is_HAT = (fun ( _discr_ ) -> (match (_discr_) with
| HAT -> begin
true
end
| _ -> begin
false
end))

let is_COLON_GREATER = (fun ( _discr_ ) -> (match (_discr_) with
| COLON_GREATER -> begin
true
end
| _ -> begin
false
end))

let is_COLON_QMARK_GREATER = (fun ( _discr_ ) -> (match (_discr_) with
| COLON_QMARK_GREATER -> begin
true
end
| _ -> begin
false
end))

let is_COLON_QMARK = (fun ( _discr_ ) -> (match (_discr_) with
| COLON_QMARK -> begin
true
end
| _ -> begin
false
end))

let is_COLON_EQUALS = (fun ( _discr_ ) -> (match (_discr_) with
| COLON_EQUALS -> begin
true
end
| _ -> begin
false
end))

let is_SEMICOLON = (fun ( _discr_ ) -> (match (_discr_) with
| SEMICOLON -> begin
true
end
| _ -> begin
false
end))

let is_GREATER_DOT = (fun ( _discr_ ) -> (match (_discr_) with
| GREATER_DOT -> begin
true
end
| _ -> begin
false
end))

let is_GREATER_BAR_RBRACK = (fun ( _discr_ ) -> (match (_discr_) with
| GREATER_BAR_RBRACK -> begin
true
end
| _ -> begin
false
end))

let is_LPAREN_STAR_RPAREN = (fun ( _discr_ ) -> (match (_discr_) with
| LPAREN_STAR_RPAREN -> begin
true
end
| _ -> begin
false
end))

let is_IFF = (fun ( _discr_ ) -> (match (_discr_) with
| IFF -> begin
true
end
| _ -> begin
false
end))

let is_IMPLIES = (fun ( _discr_ ) -> (match (_discr_) with
| IMPLIES -> begin
true
end
| _ -> begin
false
end))

let is_CONJUNCTION = (fun ( _discr_ ) -> (match (_discr_) with
| CONJUNCTION -> begin
true
end
| _ -> begin
false
end))

let is_DISJUNCTION = (fun ( _discr_ ) -> (match (_discr_) with
| DISJUNCTION -> begin
true
end
| _ -> begin
false
end))

let is_WHEN = (fun ( _discr_ ) -> (match (_discr_) with
| WHEN -> begin
true
end
| _ -> begin
false
end))

let is_WHILE = (fun ( _discr_ ) -> (match (_discr_) with
| WHILE -> begin
true
end
| _ -> begin
false
end))

let is_WITH = (fun ( _discr_ ) -> (match (_discr_) with
| WITH -> begin
true
end
| _ -> begin
false
end))

let is_HASH = (fun ( _discr_ ) -> (match (_discr_) with
| HASH -> begin
true
end
| _ -> begin
false
end))

let is_AMP = (fun ( _discr_ ) -> (match (_discr_) with
| AMP -> begin
true
end
| _ -> begin
false
end))

let is_AMP_AMP = (fun ( _discr_ ) -> (match (_discr_) with
| AMP_AMP -> begin
true
end
| _ -> begin
false
end))

let is_QUOTE = (fun ( _discr_ ) -> (match (_discr_) with
| QUOTE -> begin
true
end
| _ -> begin
false
end))

let is_LPAREN = (fun ( _discr_ ) -> (match (_discr_) with
| LPAREN -> begin
true
end
| _ -> begin
false
end))

let is_RPAREN = (fun ( _discr_ ) -> (match (_discr_) with
| RPAREN -> begin
true
end
| _ -> begin
false
end))

let is_LPAREN_RPAREN = (fun ( _discr_ ) -> (match (_discr_) with
| LPAREN_RPAREN -> begin
true
end
| _ -> begin
false
end))

let is_STAR = (fun ( _discr_ ) -> (match (_discr_) with
| STAR -> begin
true
end
| _ -> begin
false
end))

let is_COMMA = (fun ( _discr_ ) -> (match (_discr_) with
| COMMA -> begin
true
end
| _ -> begin
false
end))

let is_RARROW = (fun ( _discr_ ) -> (match (_discr_) with
| RARROW -> begin
true
end
| _ -> begin
false
end))

let is_RARROW2 = (fun ( _discr_ ) -> (match (_discr_) with
| RARROW2 -> begin
true
end
| _ -> begin
false
end))

let is_RRARROW = (fun ( _discr_ ) -> (match (_discr_) with
| RRARROW -> begin
true
end
| _ -> begin
false
end))

let is_OPEN = (fun ( _discr_ ) -> (match (_discr_) with
| OPEN -> begin
true
end
| _ -> begin
false
end))

let is_OR = (fun ( _discr_ ) -> (match (_discr_) with
| OR -> begin
true
end
| _ -> begin
false
end))

let is_PROP = (fun ( _discr_ ) -> (match (_discr_) with
| PROP -> begin
true
end
| _ -> begin
false
end))

let is_REC = (fun ( _discr_ ) -> (match (_discr_) with
| REC -> begin
true
end
| _ -> begin
false
end))

let is_THEN = (fun ( _discr_ ) -> (match (_discr_) with
| THEN -> begin
true
end
| _ -> begin
false
end))

let is_TO = (fun ( _discr_ ) -> (match (_discr_) with
| TO -> begin
true
end
| _ -> begin
false
end))

let is_TRUE = (fun ( _discr_ ) -> (match (_discr_) with
| TRUE -> begin
true
end
| _ -> begin
false
end))

let is_TRY = (fun ( _discr_ ) -> (match (_discr_) with
| TRY -> begin
true
end
| _ -> begin
false
end))

let is_EFFECT = (fun ( _discr_ ) -> (match (_discr_) with
| EFFECT -> begin
true
end
| _ -> begin
false
end))

let is_TYPE = (fun ( _discr_ ) -> (match (_discr_) with
| TYPE -> begin
true
end
| _ -> begin
false
end))

let is_KIND = (fun ( _discr_ ) -> (match (_discr_) with
| KIND -> begin
true
end
| _ -> begin
false
end))

let is_VAL = (fun ( _discr_ ) -> (match (_discr_) with
| VAL -> begin
true
end
| _ -> begin
false
end))

let is_INLINE = (fun ( _discr_ ) -> (match (_discr_) with
| INLINE -> begin
true
end
| _ -> begin
false
end))

let is_INTERFACE = (fun ( _discr_ ) -> (match (_discr_) with
| INTERFACE -> begin
true
end
| _ -> begin
false
end))

let is_INSTANCE = (fun ( _discr_ ) -> (match (_discr_) with
| INSTANCE -> begin
true
end
| _ -> begin
false
end))

let is_LAZY = (fun ( _discr_ ) -> (match (_discr_) with
| LAZY -> begin
true
end
| _ -> begin
false
end))

let is_MATCH = (fun ( _discr_ ) -> (match (_discr_) with
| MATCH -> begin
true
end
| _ -> begin
false
end))

let is_METHOD = (fun ( _discr_ ) -> (match (_discr_) with
| METHOD -> begin
true
end
| _ -> begin
false
end))

let is_MUTABLE = (fun ( _discr_ ) -> (match (_discr_) with
| MUTABLE -> begin
true
end
| _ -> begin
false
end))

let is_NEW = (fun ( _discr_ ) -> (match (_discr_) with
| NEW -> begin
true
end
| _ -> begin
false
end))

let is_NEW_EFFECT = (fun ( _discr_ ) -> (match (_discr_) with
| NEW_EFFECT -> begin
true
end
| _ -> begin
false
end))

let is_OF = (fun ( _discr_ ) -> (match (_discr_) with
| OF -> begin
true
end
| _ -> begin
false
end))

let is_EXCEPTION = (fun ( _discr_ ) -> (match (_discr_) with
| EXCEPTION -> begin
true
end
| _ -> begin
false
end))

let is_FALSE = (fun ( _discr_ ) -> (match (_discr_) with
| FALSE -> begin
true
end
| _ -> begin
false
end))

let is_FOR = (fun ( _discr_ ) -> (match (_discr_) with
| FOR -> begin
true
end
| _ -> begin
false
end))

let is_FUN = (fun ( _discr_ ) -> (match (_discr_) with
| FUN -> begin
true
end
| _ -> begin
false
end))

let is_FUNCTION = (fun ( _discr_ ) -> (match (_discr_) with
| FUNCTION -> begin
true
end
| _ -> begin
false
end))

let is_IF = (fun ( _discr_ ) -> (match (_discr_) with
| IF -> begin
true
end
| _ -> begin
false
end))

let is_IN = (fun ( _discr_ ) -> (match (_discr_) with
| IN -> begin
true
end
| _ -> begin
false
end))

let is_FINALLY = (fun ( _discr_ ) -> (match (_discr_) with
| FINALLY -> begin
true
end
| _ -> begin
false
end))

let is_DO_BANG = (fun ( _discr_ ) -> (match (_discr_) with
| DO_BANG -> begin
true
end
| _ -> begin
false
end))

let is_AND = (fun ( _discr_ ) -> (match (_discr_) with
| AND -> begin
true
end
| _ -> begin
false
end))

let is_AS = (fun ( _discr_ ) -> (match (_discr_) with
| AS -> begin
true
end
| _ -> begin
false
end))

let is_ASSERT = (fun ( _discr_ ) -> (match (_discr_) with
| ASSERT -> begin
true
end
| _ -> begin
false
end))

let is_ASR = (fun ( _discr_ ) -> (match (_discr_) with
| ASR -> begin
true
end
| _ -> begin
false
end))

let is_BEGIN = (fun ( _discr_ ) -> (match (_discr_) with
| BEGIN -> begin
true
end
| _ -> begin
false
end))

let is_DO = (fun ( _discr_ ) -> (match (_discr_) with
| DO -> begin
true
end
| _ -> begin
false
end))

let is_DONE = (fun ( _discr_ ) -> (match (_discr_) with
| DONE -> begin
true
end
| _ -> begin
false
end))

let is_DOWNTO = (fun ( _discr_ ) -> (match (_discr_) with
| DOWNTO -> begin
true
end
| _ -> begin
false
end))

let is_ELSE = (fun ( _discr_ ) -> (match (_discr_) with
| ELSE -> begin
true
end
| _ -> begin
false
end))

let is_ELIF = (fun ( _discr_ ) -> (match (_discr_) with
| ELIF -> begin
true
end
| _ -> begin
false
end))

let is_END = (fun ( _discr_ ) -> (match (_discr_) with
| END -> begin
true
end
| _ -> begin
false
end))

let is_DOT_DOT = (fun ( _discr_ ) -> (match (_discr_) with
| DOT_DOT -> begin
true
end
| _ -> begin
false
end))

let is_BAR_BAR = (fun ( _discr_ ) -> (match (_discr_) with
| BAR_BAR -> begin
true
end
| _ -> begin
false
end))

let is_LEQ = (fun ( _discr_ ) -> (match (_discr_) with
| LEQ -> begin
true
end
| _ -> begin
false
end))

let is_GEQ = (fun ( _discr_ ) -> (match (_discr_) with
| GEQ -> begin
true
end
| _ -> begin
false
end))

let is_LESSLESS = (fun ( _discr_ ) -> (match (_discr_) with
| LESSLESS -> begin
true
end
| _ -> begin
false
end))

let is_LESS = (fun ( _discr_ ) -> (match (_discr_) with
| LESS -> begin
true
end
| _ -> begin
false
end))

let is_GREATER = (fun ( _discr_ ) -> (match (_discr_) with
| GREATER -> begin
true
end
| _ -> begin
false
end))

let is_LESSGREATER = (fun ( _discr_ ) -> (match (_discr_) with
| LESSGREATER -> begin
true
end
| _ -> begin
false
end))

let is_UPCAST = (fun ( _discr_ ) -> (match (_discr_) with
| UPCAST -> begin
true
end
| _ -> begin
false
end))

let is_DOWNCAST = (fun ( _discr_ ) -> (match (_discr_) with
| DOWNCAST -> begin
true
end
| _ -> begin
false
end))

let is_NULL = (fun ( _discr_ ) -> (match (_discr_) with
| NULL -> begin
true
end
| _ -> begin
false
end))

let is_RESERVED = (fun ( _discr_ ) -> (match (_discr_) with
| RESERVED -> begin
true
end
| _ -> begin
false
end))

let is_MODULE = (fun ( _discr_ ) -> (match (_discr_) with
| MODULE -> begin
true
end
| _ -> begin
false
end))

let is_DELEGATE = (fun ( _discr_ ) -> (match (_discr_) with
| DELEGATE -> begin
true
end
| _ -> begin
false
end))

let is_CONSTRAINT = (fun ( _discr_ ) -> (match (_discr_) with
| CONSTRAINT -> begin
true
end
| _ -> begin
false
end))

let is_BASE = (fun ( _discr_ ) -> (match (_discr_) with
| BASE -> begin
true
end
| _ -> begin
false
end))

let is_SUB_EFFECT = (fun ( _discr_ ) -> (match (_discr_) with
| SUB_EFFECT -> begin
true
end
| _ -> begin
false
end))

let is_SUBTYPE = (fun ( _discr_ ) -> (match (_discr_) with
| SUBTYPE -> begin
true
end
| _ -> begin
false
end))

let is_SUBKIND = (fun ( _discr_ ) -> (match (_discr_) with
| SUBKIND -> begin
true
end
| _ -> begin
false
end))

let is_FORALL = (fun ( _discr_ ) -> (match (_discr_) with
| FORALL -> begin
true
end
| _ -> begin
false
end))

let is_EXISTS = (fun ( _discr_ ) -> (match (_discr_) with
| EXISTS -> begin
true
end
| _ -> begin
false
end))

let is_ASSUME = (fun ( _discr_ ) -> (match (_discr_) with
| ASSUME -> begin
true
end
| _ -> begin
false
end))

let is_QUERY = (fun ( _discr_ ) -> (match (_discr_) with
| QUERY -> begin
true
end
| _ -> begin
false
end))

let is_DEFINE = (fun ( _discr_ ) -> (match (_discr_) with
| DEFINE -> begin
true
end
| _ -> begin
false
end))

let is_LOGIC = (fun ( _discr_ ) -> (match (_discr_) with
| LOGIC -> begin
true
end
| _ -> begin
false
end))

let is_PRAGMALIGHT = (fun ( _discr_ ) -> (match (_discr_) with
| PRAGMALIGHT -> begin
true
end
| _ -> begin
false
end))

let is_PRAGMA_SET_OPTIONS = (fun ( _discr_ ) -> (match (_discr_) with
| PRAGMA_SET_OPTIONS -> begin
true
end
| _ -> begin
false
end))

let is_PRAGMA_RESET_OPTIONS = (fun ( _discr_ ) -> (match (_discr_) with
| PRAGMA_RESET_OPTIONS -> begin
true
end
| _ -> begin
false
end))

let is_MONADLATTICE = (fun ( _discr_ ) -> (match (_discr_) with
| MONADLATTICE -> begin
true
end
| _ -> begin
false
end))

let is_SQUIGGLY_RARROW = (fun ( _discr_ ) -> (match (_discr_) with
| SQUIGGLY_RARROW -> begin
true
end
| _ -> begin
false
end))

let is_TOTAL = (fun ( _discr_ ) -> (match (_discr_) with
| TOTAL -> begin
true
end
| _ -> begin
false
end))

let is_LET = (fun ( _discr_ ) -> (match (_discr_) with
| LET (_) -> begin
true
end
| _ -> begin
false
end))

let is_INFIX_STAR_DIV_MOD_OP = (fun ( _discr_ ) -> (match (_discr_) with
| INFIX_STAR_DIV_MOD_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_DIV_MOD_OP = (fun ( _discr_ ) -> (match (_discr_) with
| DIV_MOD_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_PREFIX_OP = (fun ( _discr_ ) -> (match (_discr_) with
| PREFIX_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_INFIX_BAR_OP = (fun ( _discr_ ) -> (match (_discr_) with
| INFIX_BAR_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_INFIX_AT_HAT_OP = (fun ( _discr_ ) -> (match (_discr_) with
| INFIX_AT_HAT_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_INFIX_COMPARE_OP = (fun ( _discr_ ) -> (match (_discr_) with
| INFIX_COMPARE_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_INFIX_STAR_STAR_OP = (fun ( _discr_ ) -> (match (_discr_) with
| INFIX_STAR_STAR_OP (_) -> begin
true
end
| _ -> begin
false
end))

let is_LANG = (fun ( _discr_ ) -> (match (_discr_) with
| LANG (_) -> begin
true
end
| _ -> begin
false
end))

let is_BASEKIND = (fun ( _discr_ ) -> (match (_discr_) with
| BASEKIND (_) -> begin
true
end
| _ -> begin
false
end))

let is_TVAR = (fun ( _discr_ ) -> (match (_discr_) with
| TVAR (_) -> begin
true
end
| _ -> begin
false
end))

let is_NAME = (fun ( _discr_ ) -> (match (_discr_) with
| NAME (_) -> begin
true
end
| _ -> begin
false
end))

let is_IDENT_LESS = (fun ( _discr_ ) -> (match (_discr_) with
| IDENT_LESS (_) -> begin
true
end
| _ -> begin
false
end))

let is_IDENT = (fun ( _discr_ ) -> (match (_discr_) with
| IDENT (_) -> begin
true
end
| _ -> begin
false
end))

let is_STRING = (fun ( _discr_ ) -> (match (_discr_) with
| STRING (_) -> begin
true
end
| _ -> begin
false
end))

let is_INT32 = (fun ( _discr_ ) -> (match (_discr_) with
| INT32 (_) -> begin
true
end
| _ -> begin
false
end))

let is_INT = (fun ( _discr_ ) -> (match (_discr_) with
| INT (_) -> begin
true
end
| _ -> begin
false
end))

let is_YIELD = (fun ( _discr_ ) -> (match (_discr_) with
| YIELD (_) -> begin
true
end
| _ -> begin
false
end))





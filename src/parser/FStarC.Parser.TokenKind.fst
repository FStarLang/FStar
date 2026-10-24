(*
   Copyright 2008-2025 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(* The kinds of tokens produced by FStarC.Parser.Lexer. Language
   extensions (e.g. Pulse) turn some identifiers into keywords of their
   own: those are [KEYWORD s], where [s] is the keyword. *)
module FStarC.Parser.TokenKind

type token_kind =
  | AMP
  | AND
  | AND_OP
  | AS
  | ASSERT
  | ASSUME
  | BACKTICK
  | BACKTICK_AT
  | BACKTICK_HASH
  | BACKTICK_PERC
  | BANG_LBRACE
  | BAR
  | BAR_RBRACE
  | BAR_RBRACK
  | BEGIN
  | BLOB
  | BY
  | CALC
  | CHAR
  | CLASS
  | COLON
  | COLON_COLON
  | COLON_EQUALS
  | COMMA
  | CONJUNCTION
  | DECREASES
  | DISJUNCTION
  | DOLLAR
  | DOT
  | DOT_DOT
  | DOT_LBRACK
  | DOT_LBRACK_BAR
  | DOT_LENS_PAREN_LEFT
  | DOT_LPAREN
  | EFFECT
  | ELIM
  | ELSE
  | END
  | ENSURES
  | EOF
  | EQUALS
  | EQUALTYPE
  | ERROR
  | EXCEPTION
  | EXISTS
  | EXISTS_OP
  | FALSE
  | FORALL
  | FORALL_OP
  | FRIEND
  | FUN
  | FUNCTION
  | HASH
  | IDENT
  | IF
  | IFF
  | IF_OP
  | IMPLIES
  | IN
  | INCLUDE
  | INLINE
  | INLINE_FOR_EXTRACTION
  | INSTANCE
  | INT
  | INT16
  | INT32
  | INT64
  | INT8
  | INTRO
  | IRREDUCIBLE
  | LARROW
  | LBRACE
  | LBRACE_BAR
  | LBRACE_COLON_PATTERN
  | LBRACE_COLON_WELL_FOUNDED
  | LBRACK
  | LBRACK_AT
  | LBRACK_AT_AT
  | LBRACK_AT_AT_AT
  | LBRACK_BAR
  | LENS_PAREN_LEFT
  | LENS_PAREN_RIGHT
  | LET
  | LET_OP
  | LOGIC
  | LONG_LEFT_ARROW
  | LPAREN
  | LPAREN_RPAREN
  | MATCH
  | MATCH_OP
  | MINUS
  | MODULE
  | NAME
  | NEW
  | NEW_EFFECT
  | NOEQUALITY
  | NOEXTRACT
  | OF
  | OPAQUE
  | OPEN
  | OPINFIX0a
  | OPINFIX0b
  | OPINFIX0c
  | OPINFIX0d
  | OPINFIX1
  | OPINFIX2
  | OPINFIX3L
  | OPINFIX3R
  | OPINFIX4
  | OPPREFIX
  | OP_MIXFIX_ACCESS
  | OP_MIXFIX_ASSIGNMENT
  | PERCENT_LBRACK
  | PIPE_LEFT
  | PIPE_RIGHT
  | PRAGMA_CHECK
  | PRAGMA_EVAL
  | PRAGMA_POP_OPTIONS
  | PRAGMA_PRINT_EFFECTS_GRAPH
  | PRAGMA_PUSH_OPTIONS
  | PRAGMA_RESET_OPTIONS
  | PRAGMA_RESTART_SOLVER
  | PRAGMA_SET_OPTIONS
  | PRAGMA_SHOW_OPTIONS
  | PRIVATE
  | QMARK
  | QMARK_DOT
  | QUOTE
  | RANGE_OF
  | RARROW
  | RBRACE
  | RBRACK
  | REAL
  | REC
  | REFLECTABLE
  | REIFIABLE
  | REIFY
  | REQUIRES
  | RETURNS
  | RETURNS_EQ
  | RPAREN
  | SEMICOLON
  | SEMICOLON_OP
  | SEQ_BANG_LBRACK
  | SET_RANGE_OF
  | SIZET
  | SPLICE
  | SPLICET
  | SQUIGGLY_RARROW
  | STRING
  | SUBKIND
  | SUBTYPE
  | SUB_EFFECT
  | SYNTH
  | THEN
  | TILDE
  | TOTAL
  | TRUE
  | TRY
  | TYPE
  | UINT16
  | UINT32
  | UINT64
  | UINT8
  | UNDERSCORE
  | UNFOLD
  | UNFOLDABLE
  | UNIV_HASH
  | UNOPTEQUALITY
  | USE_LANG_BLOB
  | VAL
  | WHEN
  | WITH
  | KEYWORD of string

(* [kind_index] is a bijection between the kinds other than [KEYWORD]
   and [0, num_kinds); it is used to index tables by kind. *)
let num_kinds : int = 173

let kind_index (k:token_kind) : int =
  match k with
  | AMP -> 0
  | AND -> 1
  | AND_OP -> 2
  | AS -> 3
  | ASSERT -> 4
  | ASSUME -> 5
  | BACKTICK -> 6
  | BACKTICK_AT -> 7
  | BACKTICK_HASH -> 8
  | BACKTICK_PERC -> 9
  | BANG_LBRACE -> 10
  | BAR -> 11
  | BAR_RBRACE -> 12
  | BAR_RBRACK -> 13
  | BEGIN -> 14
  | BLOB -> 15
  | BY -> 16
  | CALC -> 17
  | CHAR -> 18
  | CLASS -> 19
  | COLON -> 20
  | COLON_COLON -> 21
  | COLON_EQUALS -> 22
  | COMMA -> 23
  | CONJUNCTION -> 24
  | DECREASES -> 25
  | DISJUNCTION -> 26
  | DOLLAR -> 27
  | DOT -> 28
  | DOT_DOT -> 29
  | DOT_LBRACK -> 30
  | DOT_LBRACK_BAR -> 31
  | DOT_LENS_PAREN_LEFT -> 32
  | DOT_LPAREN -> 33
  | EFFECT -> 34
  | ELIM -> 35
  | ELSE -> 36
  | END -> 37
  | ENSURES -> 38
  | EOF -> 39
  | EQUALS -> 40
  | EQUALTYPE -> 41
  | ERROR -> 42
  | EXCEPTION -> 43
  | EXISTS -> 44
  | EXISTS_OP -> 45
  | FALSE -> 46
  | FORALL -> 47
  | FORALL_OP -> 48
  | FRIEND -> 49
  | FUN -> 50
  | FUNCTION -> 51
  | HASH -> 52
  | IDENT -> 53
  | IF -> 54
  | IFF -> 55
  | IF_OP -> 56
  | IMPLIES -> 57
  | IN -> 58
  | INCLUDE -> 59
  | INLINE -> 60
  | INLINE_FOR_EXTRACTION -> 61
  | INSTANCE -> 62
  | INT -> 63
  | INT16 -> 64
  | INT32 -> 65
  | INT64 -> 66
  | INT8 -> 67
  | INTRO -> 68
  | IRREDUCIBLE -> 69
  | LARROW -> 70
  | LBRACE -> 71
  | LBRACE_BAR -> 72
  | LBRACE_COLON_PATTERN -> 73
  | LBRACE_COLON_WELL_FOUNDED -> 74
  | LBRACK -> 75
  | LBRACK_AT -> 76
  | LBRACK_AT_AT -> 77
  | LBRACK_AT_AT_AT -> 78
  | LBRACK_BAR -> 79
  | LENS_PAREN_LEFT -> 80
  | LENS_PAREN_RIGHT -> 81
  | LET -> 82
  | LET_OP -> 83
  | LOGIC -> 84
  | LONG_LEFT_ARROW -> 85
  | LPAREN -> 86
  | LPAREN_RPAREN -> 87
  | MATCH -> 88
  | MATCH_OP -> 89
  | MINUS -> 90
  | MODULE -> 91
  | NAME -> 92
  | NEW -> 93
  | NEW_EFFECT -> 94
  | NOEQUALITY -> 95
  | NOEXTRACT -> 96
  | OF -> 97
  | OPAQUE -> 98
  | OPEN -> 99
  | OPINFIX0a -> 100
  | OPINFIX0b -> 101
  | OPINFIX0c -> 102
  | OPINFIX0d -> 103
  | OPINFIX1 -> 104
  | OPINFIX2 -> 105
  | OPINFIX3L -> 106
  | OPINFIX3R -> 107
  | OPINFIX4 -> 108
  | OPPREFIX -> 109
  | OP_MIXFIX_ACCESS -> 110
  | OP_MIXFIX_ASSIGNMENT -> 111
  | PERCENT_LBRACK -> 112
  | PIPE_LEFT -> 113
  | PIPE_RIGHT -> 114
  | PRAGMA_CHECK -> 115
  | PRAGMA_EVAL -> 116
  | PRAGMA_POP_OPTIONS -> 117
  | PRAGMA_PRINT_EFFECTS_GRAPH -> 118
  | PRAGMA_PUSH_OPTIONS -> 119
  | PRAGMA_RESET_OPTIONS -> 120
  | PRAGMA_RESTART_SOLVER -> 121
  | PRAGMA_SET_OPTIONS -> 122
  | PRAGMA_SHOW_OPTIONS -> 123
  | PRIVATE -> 124
  | QMARK -> 125
  | QMARK_DOT -> 126
  | QUOTE -> 127
  | RANGE_OF -> 128
  | RARROW -> 129
  | RBRACE -> 130
  | RBRACK -> 131
  | REAL -> 132
  | REC -> 133
  | REFLECTABLE -> 134
  | REIFIABLE -> 135
  | REIFY -> 136
  | REQUIRES -> 137
  | RETURNS -> 138
  | RETURNS_EQ -> 139
  | RPAREN -> 140
  | SEMICOLON -> 141
  | SEMICOLON_OP -> 142
  | SEQ_BANG_LBRACK -> 143
  | SET_RANGE_OF -> 144
  | SIZET -> 145
  | SPLICE -> 146
  | SPLICET -> 147
  | SQUIGGLY_RARROW -> 148
  | STRING -> 149
  | SUBKIND -> 150
  | SUBTYPE -> 151
  | SUB_EFFECT -> 152
  | SYNTH -> 153
  | THEN -> 154
  | TILDE -> 155
  | TOTAL -> 156
  | TRUE -> 157
  | TRY -> 158
  | TYPE -> 159
  | UINT16 -> 160
  | UINT32 -> 161
  | UINT64 -> 162
  | UINT8 -> 163
  | UNDERSCORE -> 164
  | UNFOLD -> 165
  | UNFOLDABLE -> 166
  | UNIV_HASH -> 167
  | UNOPTEQUALITY -> 168
  | USE_LANG_BLOB -> 169
  | VAL -> 170
  | WHEN -> 171
  | WITH -> 172
  | KEYWORD _ -> 173

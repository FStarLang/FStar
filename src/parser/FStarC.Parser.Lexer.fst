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

(* A hand-written lexer for F*, a port of src/ml/FStarC_Parser_LexFStar.ml.

   It emulates sedlex's longest-match semantics (ties go to the earlier
   rule) and the position conventions of FStarC_Sedlexing, so that tokens
   carry exactly the positions the Menhir parser sees.  The whole input is
   lexed up front; a lexical error becomes an ERROR token, which the parser
   raises only when it reaches it (as the lazy Menhir lexer would). *)
module FStarC.Parser.Lexer

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Show
module A   = FStar.ImmutableArray.Base
module U   = FStarC.Util
module R   = FStarC.Range
module S   = FStarC.String
module M   = FStarC.PSMap
module Uni = FStarC.Parser.Unicode
module SI  = FStarC.SmallInt
module Codes = FStarC.Errors.Codes

type extra =
  | NoExtra
  | CharLit of int
  (* ext name, contents, position after the header, position of the header start *)
  | Blob of string & string & R.pos & R.pos
  | LexError of Codes.error_code & string & R.range

(* [kind] is the name of the Menhir token (IDENT, LPAREN, ...).  [text]
   is the token payload, if any: the identifier, the operator, the
   (cleaned) numeric literal, the string literal contents, etc. *)
type token = {
  kind  : string;
  text  : string;
  sp    : R.pos;
  ep    : R.pos;
  extra : extra;
  ncom  : int; (* number of comments lexed when this token was produced *)
}

(* The UTF-8 bytes of a literal; literals are matched byte by byte *)
let cps (s:string) : list SI.t =
  let rec go (i:SI.t) : list SI.t =
    let b = S.byte_at s i in
    if SI.(b < zero) then [] else b :: go SI.(i + one)
  in
  go SI.zero

let keywords : M.t (string & string) =
  let kw k = (k, "") in
  M.of_list [
    "noeq", kw "NOEQUALITY";
    "unopteq", kw "UNOPTEQUALITY";
    "and", kw "AND";
    "assert", kw "ASSERT";
    "assume", kw "ASSUME";
    "begin", kw "BEGIN";
    "by", kw "BY";
    "calc", kw "CALC";
    "class", kw "CLASS";
    "decreases", kw "DECREASES";
    "effect", kw "EFFECT";
    "eliminate", kw "ELIM";
    "else", kw "ELSE";
    "end", kw "END";
    "ensures", kw "ENSURES";
    "exception", kw "EXCEPTION";
    "exists", kw "EXISTS";
    "false", kw "FALSE";
    "friend", kw "FRIEND";
    "forall", kw "FORALL";
    "fun", kw "FUN";
    "λ", kw "FUN";
    "function", kw "FUNCTION";
    "if", kw "IF";
    "in", kw "IN";
    "include", kw "INCLUDE";
    "inline", kw "INLINE";
    "inline_for_extraction", kw "INLINE_FOR_EXTRACTION";
    "instance", kw "INSTANCE";
    "introduce", kw "INTRO";
    "irreducible", kw "IRREDUCIBLE";
    "let", kw "LET";
    "logic", kw "LOGIC";
    "match", kw "MATCH";
    "returns", kw "RETURNS";
    "as", kw "AS";
    "module", kw "MODULE";
    "new", kw "NEW";
    "new_effect", kw "NEW_EFFECT";
    "noextract", kw "NOEXTRACT";
    "of", kw "OF";
    "open", kw "OPEN";
    "opaque", kw "OPAQUE";
    "private", kw "PRIVATE";
    "quote", kw "QUOTE";
    "range_of", kw "RANGE_OF";
    "rec", kw "REC";
    "reifiable", kw "REIFIABLE";
    "reify", kw "REIFY";
    "reflectable", kw "REFLECTABLE";
    "requires", kw "REQUIRES";
    "set_range_of", kw "SET_RANGE_OF";
    "sub_effect", kw "SUB_EFFECT";
    "synth", kw "SYNTH";
    "then", kw "THEN";
    "total", kw "TOTAL";
    "true", kw "TRUE";
    "try", kw "TRY";
    "type", kw "TYPE";
    "unfold", kw "UNFOLD";
    "unfoldable", kw "UNFOLDABLE";
    "val", kw "VAL";
    "when", kw "WHEN";
    "with", kw "WITH";
    "_", kw "UNDERSCORE";
    "α", ("IDENT", "'a");
    "β", ("IDENT", "'b");
    "γ", ("IDENT", "'c");
    "δ", ("IDENT", "'d");
    "ε", ("IDENT", "'e");
    "φ", ("IDENT", "'f");
    "χ", ("IDENT", "'g");
    "η", ("IDENT", "'h");
    "ι", ("IDENT", "'i");
    "κ", ("IDENT", "'k");
    "μ", ("IDENT", "'m");
    "ν", ("IDENT", "'n");
    "π", ("IDENT", "'p");
    "θ", ("IDENT", "'q");
    "ρ", ("IDENT", "'r");
    "σ", ("IDENT", "'s");
    "τ", ("IDENT", "'t");
    "ψ", ("IDENT", "'u");
    "ω", ("IDENT", "'w");
    "ξ", ("IDENT", "'x");
    "ζ", ("IDENT", "'z");
  ]

let constructors : M.t (string & string) =
  M.of_list [
    "ℕ", ("IDENT", "nat");
    "ℤ", ("IDENT", "int");
    "𝔹", ("IDENT", "bool");
  ]

(* The ASCII operator tokens (op_token_1..5 in the sedlex lexer). *)
let op_tokens : list (string & string & string) = [
  "~", "TILDE", "~";
  "-", "MINUS", "";
  "/\\", "CONJUNCTION", "";
  "\\/", "DISJUNCTION", "";
  "<:", "SUBTYPE", "";
  "$:", "EQUALTYPE", "";
  "<@", "SUBKIND", "";
  "(|", "LENS_PAREN_LEFT", "";
  "|)", "LENS_PAREN_RIGHT", "";
  "#", "HASH", "";
  "u#", "UNIV_HASH", "";
  "&", "AMP", "";
  "()", "LPAREN_RPAREN", "";
  "(", "LPAREN", "";
  ")", "RPAREN", "";
  ",", "COMMA", "";
  "~>", "SQUIGGLY_RARROW", "";
  "->", "RARROW", "";
  "<--", "LONG_LEFT_ARROW", "";
  "<-", "LARROW", "";
  "<==>", "IFF", "";
  "==>", "IMPLIES", "";
  ".", "DOT", "";
  "?.", "QMARK_DOT", "";
  "?", "QMARK", "";
  ".[|", "DOT_LBRACK_BAR", "";
  ".[", "DOT_LBRACK", "";
  ".(|", "DOT_LENS_PAREN_LEFT", "";
  ".(", "DOT_LPAREN", "";
  "$", "DOLLAR", "";
  "{:pattern", "LBRACE_COLON_PATTERN", "";
  "{:well-founded", "LBRACE_COLON_WELL_FOUNDED", "";
  ":", "COLON", "";
  "::", "COLON_COLON", "";
  ":=", "COLON_EQUALS", "";
  ";", "SEMICOLON", "";
  "=", "EQUALS", "";
  "%[", "PERCENT_LBRACK", "";
  "returns$", "RETURNS_EQ", "";
  "!{", "BANG_LBRACE", "";
  "[@@@", "LBRACK_AT_AT_AT", "";
  "[@@", "LBRACK_AT_AT", "";
  "[@", "LBRACK_AT", "";
  "[|", "LBRACK_BAR", "";
  "{|", "LBRACE_BAR", "";
  "[", "LBRACK", "";
  "|>", "PIPE_RIGHT", "";
  "]", "RBRACK", "";
  "|]", "BAR_RBRACK", "";
  "|}", "BAR_RBRACE", "";
  "{", "LBRACE", "";
  "|", "BAR", "";
  "}", "RBRACE", "";
]

let op_token_cps : list (list SI.t & string & string) =
  List.map (fun (s, k, t) -> (cps s, k, t)) op_tokens

(* Unicode operators; only reachable through the [uoperator] rule, i.e.,
   for single non-ASCII math symbols. *)
let uoperators : M.t (string & string) =
  M.of_list [
    "∀", ("FORALL", "");
    "∃", ("EXISTS", "");
    "⊤", ("NAME", "True");
    "⊥", ("NAME", "False");
    "⟹", ("IMPLIES", "");
    "⟺", ("IFF", "");
    "→", ("RARROW", "");
    "←", ("LARROW", "");
    "⟵", ("LONG_LEFT_ARROW", "");
    "↝", ("SQUIGGLY_RARROW", "");
    "≔", ("COLON_EQUALS", "");
    "∧", ("CONJUNCTION", "");
    "∨", ("DISJUNCTION", "");
    "¬", ("TILDE", "~");
    "⸬", ("COLON_COLON", "");
    "▹", ("PIPE_RIGHT", "");
    "÷", ("OPINFIX3L", "÷");
    "‖", ("OPINFIX0a", "||");
    "×", ("IDENT", "op_Star");
    "∗", ("OPINFIX3L", "*");
    "⇒", ("OPINFIX0c", "=>");
    "≥", ("OPINFIX0c", ">=");
    "≤", ("OPINFIX0c", "<=");
    "≠", ("OPINFIX0c", "<>");
    "≪", ("OPINFIX0c", "<<");
    "◃", ("OPINFIX0c", "<|");
    "±", ("OPPREFIX", "±");
    "∁", ("OPPREFIX", "∁");
    "∂", ("OPPREFIX", "∂");
    "√", ("OPPREFIX", "√");
  ]

(* Fixed literal tokens that come first in the sedlex rule list. *)
let early_literals : list (list SI.t & string) =
  List.map (fun (s, k) -> (cps s, k)) [
    "%splice", "SPLICE";
    "%splice_t", "SPLICET";
    "`%", "BACKTICK_PERC";
    "`#", "BACKTICK_HASH";
    "`@", "BACKTICK_AT";
    "seq![", "SEQ_BANG_LBRACK";
    "#show-options", "PRAGMA_SHOW_OPTIONS";
    "#set-options", "PRAGMA_SET_OPTIONS";
    "#reset-options", "PRAGMA_RESET_OPTIONS";
    "#push-options", "PRAGMA_PUSH_OPTIONS";
    "#pop-options", "PRAGMA_POP_OPTIONS";
    "#restart-solver", "PRAGMA_RESTART_SOLVER";
    "#print-effects-graph", "PRAGMA_PRINT_EFFECTS_GRAPH";
    "#check", "PRAGMA_CHECK";
    "#eval", "PRAGMA_EVAL";
  ]

(* "match", "if", ... followed by operator characters *)
let kw_op_rules : list (list SI.t & string & string) =
  List.map (fun (s, k, kop) -> (cps s, k, kop)) [
    "match", "MATCH", "MATCH_OP";
    "if", "IF", "IF_OP";
    "let", "LET", "LET_OP";
    "exists", "EXISTS", "EXISTS_OP";
    "∃", "EXISTS", "EXISTS_OP";
    "forall", "FORALL", "FORALL_OP";
    "∀", "FORALL", "FORALL_OP";
    "and", "AND", "AND_OP";
    ";", "SEMICOLON", "SEMICOLON_OP";
  ]

let mixfix_rules : list (list SI.t & string) =
  List.map (fun (s, k) -> (cps s, k)) [
    ".[]<-", "OP_MIXFIX_ASSIGNMENT";
    ".()<-", "OP_MIXFIX_ASSIGNMENT";
    ".(||)<-", "OP_MIXFIX_ASSIGNMENT";
    ".[||]<-", "OP_MIXFIX_ASSIGNMENT";
    ".[]", "OP_MIXFIX_ACCESS";
    ".()", "OP_MIXFIX_ACCESS";
    ".(||)", "OP_MIXFIX_ACCESS";
    ".[||]", "OP_MIXFIX_ACCESS";
  ]

let cps_source_file = cps "__SOURCE_FILE__"
let cps_line = cps "__LINE__"
let cps_fileline = cps "__FILELINE__"
let cps_lang = cps "#lang-"
let cps_in_fstar = cps "// IN F*:"
let cps_number_strip = cps "uzyslLUnIN"
let ops_prefix = cps "!~?"
let ops_0a = cps "|"
let ops_0b = cps "&"
let ops_0c = cps "=<"
let ops_0d = cps "$"
let ops_1 = cps "@^"
let ops_2 = cps "+-"
let ops_3 = cps "*/%"
let lit_0 = cps "!$%&*+-.<>=?^|~:@#\\/"
let lit_1 = cps "!~?|&=<>$@^+-*/%.:"
let lit_2 = cps "\\\"'bfntrv0"
let lit_3 = cps "LF"
let lit_4 = cps "*)"
let lit_5 = cps "(*"
let lit_6 = cps "```"
let lit_7 = cps ";;"
let lit_8 = cps "y"
let lit_9 = cps "z"
let lit_10 = cps "s"
let lit_11 = cps "l"
let lit_12 = cps "L"
let lit_13 = cps "sz"
let lit_14 = cps "//"
let lit_15 = cps "<|"
let lit_16 = cps "|>"
let lit_17 = cps ".."
let lit_18 = cps "**"
let lit_19 = cps "|->"

open FStarC.SmallInt

inline_for_extraction
let ch (c:FStar.Char.char) : t = of_char c

let mem_cp (c:t) (l:list t) : bool = FStar.List.Tot.existsb (fun d -> d = c) l

let op_char_cps = lit_0
let symbolchar_cps = lit_1

let is_digit (c:t) : bool = c >= ch '0' && c <= ch '9'
let is_hex (c:t) : bool =
  is_digit c || (c >= ch 'A' && c <= ch 'F') || (c >= ch 'a' && c <= ch 'f')
let rec upto (n:t) (k:t) : list t = if k >= n then [] else k :: upto n (k + one)

let ascii_limit : t = of_int 128

(* Membership tables for ASCII character classes *)
let ascii_table (l:list t) : A.t bool =
  A.of_list (FStar.List.Tot.map (fun c -> mem_cp c l) (upto ascii_limit zero))
let in_table (tbl:A.t bool) (c:t) : ML bool =
  c >= zero && c < ascii_limit && U.array_index tbl (to_int c)

let op_char_tab = ascii_table op_char_cps
let symbolchar_tab = ascii_table symbolchar_cps
let is_op_char (c:t) : ML bool = in_table op_char_tab c
let is_symbolchar (c:t) : ML bool = in_table symbolchar_tab c

let is_lower (c:t) : ML bool =
  if c < ascii_limit then c >= ch 'a' && c <= ch 'z' else Uni.is_ll (to_int c)
let is_ident_start (c:t) : ML bool =
  c = ch '_' || c = ch '\'' || is_lower c
let is_constructor_start (c:t) : ML bool =
  if c < zero then false
  else if c < ascii_limit then c >= ch 'A' && c <= ch 'Z'
  else Uni.is_lu (to_int c) || Uni.is_lt (to_int c)
let is_ident_char (c:t) : ML bool =
  if c < zero then false
  else if c < ascii_limit then
    (c >= ch 'a' && c <= ch 'z') || (c >= ch 'A' && c <= ch 'Z') || is_digit c ||
    c = ch '\'' || c = ch '_'
  else
    let c = to_int c in
    Uni.is_ll c || Uni.is_lu c || Uni.is_lo c || Uni.is_lm c
let is_anywhite (c:t) : ML bool =
  c = ch ' ' || c = ch '\t' || c = of_int 11 || c = of_int 12 ||
  c = of_int 0xA0 || c = of_int 0xFEFF ||
  (c >= ascii_limit && Uni.is_zs (to_int c))
let is_newline_char (c:t) : bool =
  c = ch '\n' || c = ch '\r' || c = of_int 0x2028 || c = of_int 0x2029
let is_uoperator (c:t) : ML bool =
  c >= ascii_limit && Uni.is_sm (to_int c)

(* Trim each line of a comment by the indentation of its first line,
   if possible (maybe_trim_lines in the sedlex lexer).  Only leading
   spaces are trimmed, so byte offsets and columns agree. *)
let maybe_trim_lines (start_column:t) (comment:string) : ML string =
  if start_column = zero then comment
  else
    let lines = S.split ['\n'] comment in
    let ensures_empty_prefix (k:t) (s:string) : ML t =
      let j = min k (S.byte_length s - one) in
      let rec aux (i:t) : ML t =
        if i > j then k
        else if S.byte_at s i <> ch ' ' then i
        else aux (i + one)
      in
      aux zero
    in
    let trim_width = List.fold_left ensures_empty_prefix start_column lines in
    let tail (s:string) : ML string =
      let n = S.byte_length s in
      if trim_width >= n then "" else S.byte_substring s trim_width n
    in
    S.concat "\n" (List.map tail lines)

exception LexFail of Codes.error_code & string & R.range

noeq
type lstate = {
  buf       : string;
  len       : t;
  fname     : string;
  cur       : ref t;
  lnum      : ref t;
  bol       : ref t; (* the offset of the beginning of the current line *)
  bol_col   : ref t; (* its column *)
  (* A position on the current line and its column, so that columns
     are computed incrementally *)
  cache_off : ref t;
  cache_col : ref t;
  comments  : ref (list (string & R.range));
  ncomments : ref t;
}

(* The character at [i], or -1 at the end of the input *)
let get (st:lstate) (i:t) : t = S.code_point_at st.buf i
(* The byte at [i]; when comparing against ASCII characters, cheaper
   than [get] *)
let byte (st:lstate) (i:t) : t = S.byte_at st.buf i
(* The offset of the character after the one at [i] *)
let next (st:lstate) (i:t) : t = S.next_code_point st.buf i

let lexeme (st:lstate) (i j:t) : string = S.byte_substring st.buf i j

(* The number of characters in the bytes [i, j), plus [n] *)
let rec count_chars (st:lstate) (i j n:t) : t =
  if i >= j then n
  else
    let b = byte st i in
    let is_continuation = b >= of_int 0x80 && b < of_int 0xC0 in
    count_chars st (i + one) j (if is_continuation then n else n + one)

(* The column of offset [i], in characters as Sedlexing counts them *)
let col_of (st:lstate) (i:t) : ML t =
  if i < !st.bol then i - !st.bol (* clamped to 0 by mk_pos *)
  else begin
    let c =
      if i >= !st.cache_off then count_chars st !st.cache_off i !st.cache_col
      else count_chars st !st.bol i !st.bol_col
    in
    st.cache_off := i;
    st.cache_col := c;
    c
  end

(* The position of an offset, as Sedlexing would report it *)
let pos_of (st:lstate) (i:t) : ML R.pos =
  R.mk_pos (to_int !st.lnum) (to_int (col_of st i))

let cur_pos (st:lstate) : ML R.pos = pos_of st !st.cur

let new_line (st:lstate) : ML unit =
  st.lnum := !st.lnum + one;
  st.bol := !st.cur;
  st.bol_col := zero;
  st.cache_off := !st.cur;
  st.cache_col := zero

let mk_range (st:lstate) (p1 p2:R.pos) : R.range = R.mk_range st.fname p1 p2

let add_comment (st:lstate) (s:string) (r:R.range) : ML unit =
  st.comments := (s, r) :: !st.comments;
  st.ncomments := !st.ncomments + one

(* ---------------------------------------------------------------------- *)
(* Matchers: given a start offset, return the end offset, or -1           *)
(* ---------------------------------------------------------------------- *)

let match_lit (st:lstate) (l:list t) (i:t) : ML t =
  let rec go (l:list t) (i:t) : ML t =
    match l with
    | [] -> i
    | c :: l -> if byte st i = c then go l (i + one) else minus_one
  in
  go l i

let rec star (st:lstate) (f:t -> ML bool) (i:t) : ML t =
  if f (get st i) then star st f (next st i) else i

let plus (st:lstate) (f:t -> ML bool) (i:t) : ML t =
  if f (get st i) then star st f (next st i) else minus_one

let match_newline (st:lstate) (i:t) : ML t =
  let c = get st i in
  if c = ch '\r' && byte st (i + one) = ch '\n' then i + of_int 2
  else if is_newline_char c then next st i
  else minus_one

let match_ident (st:lstate) (i:t) : ML t =
  if is_ident_start (get st i) then star st is_ident_char (next st i) else minus_one

let match_constructor (st:lstate) (i:t) : ML t =
  if is_constructor_start (get st i) then star st is_ident_char (next st i) else minus_one

(* escape_char = '\\', (Chars "\\\"'bfntrv0" | "x", hex, hex | "u", hex, hex, hex, hex) *)
let match_escape (st:lstate) (i:t) : ML t =
  if byte st i <> ch '\\' then minus_one
  else
    let c = byte st (i + one) in
    let hex (k:int) : ML bool = is_hex (byte st (i + of_int k)) in
    if mem_cp c lit_2 then i + of_int 2
    else if c = ch 'x' && hex 2 && hex 3 then i + of_int 4
    else if c = ch 'u' && hex 2 && hex 3 && hex 4 && hex 5 then i + of_int 6
    else minus_one

(* char = Compl '\\' | escape_char *)
let match_char (st:lstate) (i:t) : ML t =
  let c = get st i in
  if c < zero then minus_one
  else if c <> ch '\\' then next st i
  else match_escape st i

let match_char_lit (st:lstate) (i:t) (with_b:bool) : ML t =
  if byte st i <> ch '\'' then minus_one
  else
    let j = match_char st (i + one) in
    if j < zero || byte st j <> ch '\'' then minus_one
    else if with_b then (if byte st (j + one) = ch 'B' then j + of_int 2 else minus_one)
    else j + one

let match_integer (st:lstate) (i:t) : ML t = plus st (fun c -> is_digit c) i

let match_xinteger (st:lstate) (i:t) : ML t =
  if byte st i <> ch '0' then minus_one
  else
    let c = byte st (i + one) in
    let j = i + of_int 2 in
    if c = ch 'x' || c = ch 'X' then plus st (fun c -> is_hex c) j
    else if c = ch 'o' || c = ch 'O' then plus st (fun c -> c >= ch '0' && c <= ch '7') j
    else if c = ch 'b' || c = ch 'B' then plus st (fun c -> c = ch '0' || c = ch '1') j
    else minus_one

let any_integer_ends (st:lstate) (i:t) : ML (list t) =
  List.filter (fun e -> e >= zero) [match_integer st i; match_xinteger st i]

let max_list (l:list t) : t = FStar.List.Tot.fold_left (fun a b -> if b > a then b else a) minus_one l

(* any_integer followed by the given suffix *)
let match_int_suffix (st:lstate) (i:t) (suffix:list t) : ML t =
  max_list (List.map (fun e -> match_lit st suffix e) (any_integer_ends st i))

let match_int_usuffix (st:lstate) (i:t) (suffix:list t) : ML t =
  max_list (List.map (fun e ->
    let c = byte st e in
    if c = ch 'u' || c = ch 'U' then match_lit st suffix (e + one) else minus_one)
    (any_integer_ends st i))

(* floatp = Plus digit, '.', Star digit *)
let match_floatp (st:lstate) (i:t) : ML t =
  let j = match_integer st i in
  if j < zero || byte st j <> ch '.' then minus_one
  else star st (fun c -> is_digit c) (j + one)

(* The offset after an optional sign at [k] *)
let skip_sign (st:lstate) (k:t) : ML t =
  let c = byte st k in
  if c = ch '+' || c = ch '-' then k + one else k

let is_e (c:t) : bool = c = ch 'e' || c = ch 'E'

(* floate = Plus digit, Opt ('.', Star digit), Chars "eE", Opt (Chars "+-"), Plus digit *)
let match_floate (st:lstate) (i:t) : ML t =
  let j = match_integer st i in
  if j < zero then minus_one
  else
    let exp (k:t) : ML t =
      if is_e (byte st k) then match_integer st (skip_sign st (k + one))
      else minus_one
    in
    let without_dot = exp j in
    let with_dot =
      if byte st j = ch '.' then exp (star st (fun c -> is_digit c) (j + one)) else minus_one
    in
    max without_dot with_dot

let match_real (st:lstate) (i:t) : ML t =
  let j = match_floatp st i in
  if j >= zero && byte st j = ch 'R' then j + one else minus_one

(* (integer | xinteger | ieee64 | xieee64), Plus ident_char *)
let match_bad_number (st:lstate) (i:t) : ML t =
  let xi = match_xinteger st i in
  let xieee = if xi >= zero then match_lit st (lit_3) xi else minus_one in
  (* sedlex considers every way of splitting the input; since digits are
     ident chars, the shortest float matches are the relevant ones. *)
  let j = match_integer st i in
  let floatp_min = if j >= zero && byte st j = ch '.' then j + one else minus_one in
  let exp_min (k:t) : ML t =
    if is_e (byte st k) then
      let k = skip_sign st (k + one) in
      if is_digit (byte st k) then k + one else minus_one
    else minus_one
  in
  let floate_min =
    if j < zero then minus_one
    else if floatp_min < zero then exp_min j
    else max (exp_min j) (exp_min (star st (fun c -> is_digit c) floatp_min))
  in
  let ends = [match_integer st i; xi; match_floatp st i; match_floate st i; xieee; floatp_min; floate_min] in
  max_list (List.map (fun e -> if e < zero then minus_one else plus st is_ident_char e) ends)

(* '`', '`', Plus (Compl ('`' | nl) | '`', Compl ('`' | nl)), '`', '`' *)
let match_backtick_ident (st:lstate) (i:t) : ML t =
  if byte st i <> ch '`' || byte st (i + one) <> ch '`' then minus_one
  else
    let ok (c:t) = c >= zero && c <> ch '`' && not (is_newline_char c) in
    let rec go (j:t) (n:t) : ML t =
      let c = get st j in
      if ok c then go (next st j) (n + one)
      else if c = ch '`' && ok (get st (j + one)) then go (next st (j + one)) (n + one)
      else if n > zero && c = ch '`' && byte st (j + one) = ch '`' then j + of_int 2
      else minus_one
    in
    go (i + of_int 2) zero

(* Truncate a match [i, e) at the first occurrence of "//" *)
let no_comment (st:lstate) (i e:t) : ML t =
  let rec go (j:t) : ML t =
    if j + one >= e then e
    else if byte st j = ch '/' && byte st (j + one) = ch '/' then j
    else go (j + one)
  in
  go i

(* ---------------------------------------------------------------------- *)
(* Rules                                                                  *)
(* ---------------------------------------------------------------------- *)

type rule =
  | REarly of string
  | RTripleBacktick
  | RLang
  | RSourceFile
  | RLine
  | RFileLine
  | RWhite
  | RNewline
  | RCharLit
  | RCharLitB
  | RBacktick
  | RKwOp of t & string & string (* keyword length, plain kind, op kind *)
  | RSemiSemi
  | RIdent
  | RConstructor
  | RInt
  | RUInt8
  | RNumber of string
  | RReal
  | RBadNumber
  | RCommentStart
  | RInFStar
  | RLineComment
  | RString
  | RBacktickIdent
  | RPipeLeft
  | RPipeRight
  | RDotDot
  | ROpToken of string & string
  | RLt
  | RGt
  | ROp of string
  | RUOperator
  | RMixfix of string
  | REof
  | RAny

let tok (k:string) (txt:string) (sp ep:R.pos) (n:t) : token =
  { kind = k; text = txt; sp = sp; ep = ep; extra = NoExtra; ncom = to_int n }

(* The character denoted by the (escaped) character at [i] *)
let unescape (st:lstate) (i:t) : ML t =
  if byte st i <> ch '\\' then get st i
  else
    let c = byte st (i + one) in
    if c = ch '0' then zero
    else if c = ch 'b' then of_int 8
    else if c = ch 't' then of_int 9
    else if c = ch 'n' then of_int 10
    else if c = ch 'v' then of_int 11
    else if c = ch 'f' then of_int 12
    else if c = ch 'r' then of_int 13
    else if c = ch 'u' || c = ch 'x' then
      let n = if c = ch 'u' then of_int 4 else of_int 2 in
      let k = i + of_int 2 in
      of_int (U.int_of_string ("0x" ^ lexeme st k (k + n)))
    else get st (i + one)

let string_of_cp (c:t) : ML string = S.string_of_list [U.char_of_int (to_int c)]

(* Strip the suffixes and prefixes of numeric literals *)
let clean_number (s:string) : ML string =
  let n = S.byte_length s in
  let strip (i:t) : bool = mem_cp (S.byte_at s i) cps_number_strip in
  let rec left (i:t) : ML t = if i < n && strip i then left (i + one) else i in
  let rec right (j:t) : ML t = if j > zero && strip (j - one) then right (j - one) else j in
  S.byte_substring s (left zero) (right n)

let lex_error (#a:Type) (st:lstate) (code:Codes.error_code) (msg:string) (p1 p2:R.pos) : ML a =
  raise (LexFail (code, msg, mk_range st p1 p2))

(* The end of the run of characters starting at [i] that are not EOF and
   do not satisfy [stop] *)
let rec run_end (st:lstate) (stop:t -> ML bool) (i:t) : ML t =
  let c = get st i in
  if c < zero || stop c then i else run_end st stop (next st i)

let chunks_to_string (l:list string) : ML string = S.concat "" (List.rev l)

let comment_stop (c:t) : ML bool =
  c = ch '(' || c = ch '*' || is_newline_char c

(* Nested comments.  Faithful to the sedlex lexer, including its handling
   of nested comments: closing an inner comment emits the comment
   accumulated so far.  [buf] holds the chunks read so far, in reverse. *)
let rec comment (st:lstate) (inner:bool) (buf:ref (list string)) (startpos:R.pos) (startcol:t) : ML unit =
  let i = !st.cur in
  let terminate () : ML unit =
    let endpos = cur_pos st in
    let s = chunks_to_string ("*)" :: !buf) in
    buf := [];
    add_comment st (maybe_trim_lines startcol s) (mk_range st startpos endpos)
  in
  let j = run_end st comment_stop i in
  if j > i then begin
    buf := lexeme st i j :: !buf;
    st.cur := j;
    comment st inner buf startpos startcol
  end else
  let c = byte st i in
  if c = ch '(' && byte st (i + one) = ch '*' then begin
    buf := "(*" :: !buf;
    st.cur := i + of_int 2;
    comment st true buf startpos startcol;
    comment st inner buf startpos startcol
  end else
  let nl = match_newline st i in
  if nl >= zero then begin
    st.cur := nl;
    new_line st;
    buf := lexeme st i nl :: !buf;
    comment st inner buf startpos startcol
  end else if c = ch '*' && byte st (i + one) = ch ')' then begin
    st.cur := i + of_int 2;
    terminate ()
  end else if i >= st.len then
    terminate ()
  else begin
    let j = next st i in
    buf := lexeme st i j :: !buf;
    st.cur := j;
    comment st inner buf startpos startcol
  end

let line_comment (st:lstate) (pre:string) : ML unit =
  let i = !st.cur in
  let j = run_end st is_newline_char i in
  let sp = pos_of st i in
  let ep = pos_of st j in
  st.cur := j;
  add_comment st (pre ^ lexeme st i j) (mk_range st sp ep)

let string_stop (c:t) : ML bool =
  c = ch '\\' || c = ch '"' || is_newline_char c

(* [acc] holds the chunks of the literal read so far, in reverse *)
let rec string_lit (st:lstate) (acc:list string) (sp:R.pos) : ML token =
  let i = !st.cur in
  let j = run_end st string_stop i in
  if j > i then begin
    st.cur := j;
    string_lit st (lexeme st i j :: acc) sp
  end else
  let c = get st i in
  let nl1 = if c = ch '\\' then match_newline st (i + one) else minus_one in
  if nl1 >= zero then begin
    st.cur := star st is_anywhite nl1;
    new_line st;
    string_lit st acc sp
  end else
  let nl = match_newline st i in
  if nl >= zero then begin
    st.cur := nl;
    new_line st;
    string_lit st (lexeme st i nl :: acc) sp
  end else
  let esc = match_escape st i in
  if esc >= zero then begin
    st.cur := esc;
    string_lit st (string_of_cp (unescape st i) :: acc) sp
  end else if c = ch '"' then begin
    st.cur := i + one;
    tok "STRING" (chunks_to_string acc) sp (cur_pos st) !st.ncomments
  end else if c < zero then
    lex_error st Codes.Fatal_SyntaxError "unterminated string" (cur_pos st) (cur_pos st)
  else begin
    (* a backslash that does not start an escape *)
    st.cur := i + one;
    string_lit st (lexeme st i (i + one) :: acc) sp
  end

let blob_stop (c:t) : ML bool = c = ch '`' || is_newline_char c

(* [acc] holds the chunks read so far, in reverse *)
let rec blob (st:lstate) (acc:list string) (name:string) (pos snap:R.pos) : ML token =
  let i = !st.cur in
  if match_lit st (lit_6) i >= zero then begin
    let sp = cur_pos st in
    st.cur := i + of_int 3;
    { (tok "BLOB" name sp (cur_pos st) !st.ncomments) with
      extra = Blob (name, chunks_to_string acc, pos, snap) }
  end else if i >= st.len then
    lex_error st Codes.Fatal_SyntaxError "Syntax error: unterminated extension syntax"
      (cur_pos st) (cur_pos st)
  else
    let j = run_end st blob_stop i in
    let j = if j > i then j else next st i in
    let nl = match_newline st i in
    if nl >= zero then begin
      st.cur := nl;
      new_line st;
      blob st (lexeme st i nl :: acc) name pos snap
    end else begin
      st.cur := j;
      blob st (lexeme st i j :: acc) name pos snap
    end

(* [acc] holds the chunks read so far, in reverse *)
let rec use_lang (st:lstate) (acc:list string) (name:string) (pos snap:R.pos) : ML token =
  let i = !st.cur in
  if i >= st.len then
    let p = cur_pos st in
    { (tok "USE_LANG_BLOB" name p p !st.ncomments) with
      extra = Blob (name, chunks_to_string acc, pos, snap) }
  else
    let j = run_end st is_newline_char i in
    if j > i then begin
      st.cur := j;
      use_lang st (lexeme st i j :: acc) name pos snap
    end else begin
      let nl = match_newline st i in
      st.cur := nl;
      new_line st;
      use_lang st (lexeme st i nl :: acc) name pos snap
    end

(* Literal tables bucketed by their first (ASCII) byte, so that [select]
   only tries the literals that can match.  Literals starting with a
   non-ASCII character are tried for every non-ASCII input. *)
let first_cp (l:list t) : t = match l with c :: _ -> c | [] -> minus_one

let bucket (#a:Type) (first:a -> t) (l:list a) : ML (A.t (list a) & list a) =
  (A.of_list (List.map (fun c -> List.filter (fun x -> first x = c) l) (upto ascii_limit zero)),
   List.filter (fun x -> first x >= ascii_limit) l)

let lookup (#a:Type) (b:A.t (list a) & list a) (c:t) : ML (list a) =
  if c < zero then []
  else if c < ascii_limit then U.array_index (fst b) (to_int c)
  else snd b

let early_bucket = bucket (fun (l, _) -> first_cp l) early_literals
let kw_op_bucket = bucket (fun (l, _, _) -> first_cp l) kw_op_rules
let op_token_bucket = bucket (fun (l, _, _) -> first_cp l) op_token_cps
let mixfix_bucket = bucket (fun (l, _) -> first_cp l) mixfix_rules

let select (st:lstate) (i:t) : ML (rule & t) =
  let c = get st i in
  (* Fast paths: rules that are the only ones starting with [c] *)
  if c = ch ' ' || c = ch '\t' || c = of_int 11 || c = of_int 12 then (RWhite, plus st is_anywhite i)
  else if c = ch '\n' || c = ch '\r' then (RNewline, match_newline st i)
  else
  let best_r : ref rule = mk_ref RAny in
  let best_e : ref t = mk_ref minus_one in
  let try_ (r:rule) (e:t) : ML unit =
    if e > i && e > !best_e then (best_r := r; best_e := e)
  in
  List.iter (fun (l, k) -> try_ (REarly k) (match_lit st l i)) (lookup early_bucket c);
  if c = ch '`' then begin
    let e = match_lit st (lit_6) i in
    if e >= zero then try_ RTripleBacktick (match_ident st e)
  end;
  if c = ch '#' then begin
    let e = match_lit st cps_lang i in
    if e >= zero then try_ RLang (match_ident st e)
  end;
  if c = ch '_' then begin
    try_ RSourceFile (match_lit st cps_source_file i);
    try_ RLine (match_lit st cps_line i);
    try_ RFileLine (match_lit st cps_fileline i)
  end;
  if c >= ascii_limit then begin
    try_ RWhite (plus st is_anywhite i);
    try_ RNewline (match_newline st i)
  end;
  if c = ch '\'' then begin
    try_ RCharLit (match_char_lit st i false);
    try_ RCharLitB (match_char_lit st i true)
  end;
  try_ RBacktick (if c = ch '`' then i + one else minus_one);
  List.iter (fun (l, k, kop) ->
    let e = match_lit st l i in
    if e >= zero then try_ (RKwOp (e - i, k, kop)) (plus st (fun c -> is_op_char c) e))
    (lookup kw_op_bucket c);
  if c = ch ';' then try_ RSemiSemi (match_lit st (lit_7) i);
  try_ RIdent (match_ident st i);
  try_ RConstructor (match_constructor st i);
  if is_digit c then begin
    try_ RInt (max_list (any_integer_ends st i));
    try_ RUInt8 (max (match_int_usuffix st i (lit_8)) (match_int_suffix st i (lit_9)));
    try_ (RNumber "INT8") (match_int_suffix st i (lit_8));
    try_ (RNumber "UINT16") (match_int_usuffix st i (lit_10));
    try_ (RNumber "INT16") (match_int_suffix st i (lit_10));
    try_ (RNumber "UINT32") (match_int_usuffix st i (lit_11));
    try_ (RNumber "INT32") (match_int_suffix st i (lit_11));
    try_ (RNumber "UINT64") (match_int_usuffix st i (lit_12));
    try_ (RNumber "INT64") (match_int_suffix st i (lit_12));
    try_ (RNumber "SIZET") (match_int_suffix st i (lit_13));
    try_ RReal (match_real st i);
    try_ RBadNumber (match_bad_number st i)
  end;
  if c = ch '(' then try_ RCommentStart (match_lit st (lit_5) i);
  if c = ch '/' then begin
    try_ RInFStar (match_lit st cps_in_fstar i);
    try_ RLineComment (match_lit st (lit_14) i)
  end;
  try_ RString (if c = ch '"' then i + one else minus_one);
  if c = ch '`' then try_ RBacktickIdent (match_backtick_ident st i);
  if c = ch '<' then try_ RPipeLeft (match_lit st (lit_15) i);
  if c = ch '|' then try_ RPipeRight (match_lit st (lit_16) i);
  if c = ch '.' then try_ RDotDot (match_lit st (lit_17) i);
  List.iter (fun (l, k, t) -> try_ (ROpToken (k, t)) (match_lit st l i)) (lookup op_token_bucket c);
  if is_op_char c then begin
    try_ RLt (if c = ch '<' then i + one else minus_one);
    try_ RGt (if c = ch '>' then star st (fun c -> is_symbolchar c) (i + one) else minus_one);
    let sym_after (e:t) : ML t = if e < zero then minus_one else star st (fun c -> is_symbolchar c) e in
    let one_of (chars:list t) : t = if mem_cp c chars then i + one else minus_one in
    try_ (ROp "OPINFIX3R") (sym_after (match_lit st (lit_18) i));
    try_ (ROp "OPINFIX4") (sym_after (match_lit st (lit_19) i));
    try_ (ROp "OPPREFIX") (sym_after (one_of ops_prefix));
    try_ (ROp "OPINFIX0a") (sym_after (one_of ops_0a));
    try_ (ROp "OPINFIX0b") (sym_after (one_of ops_0b));
    try_ (ROp "OPINFIX0c") (sym_after (one_of ops_0c));
    try_ (ROp "OPINFIX0d") (sym_after (one_of ops_0d));
    try_ (ROp "OPINFIX1") (sym_after (one_of ops_1));
    try_ (ROp "OPINFIX2") (sym_after (one_of ops_2));
    try_ (ROp "OPINFIX3L") (sym_after (one_of ops_3))
  end;
  if c >= ascii_limit then try_ RUOperator (if is_uoperator c then next st i else minus_one);
  List.iter (fun (l, k) -> try_ (RMixfix k) (match_lit st l i)) (lookup mixfix_bucket c);
  (!best_r, !best_e)

(* Produce the next token; whitespace and comments are skipped. *)
let rec next_token (st:lstate) : ML token =
  let i = !st.cur in
  let sp = cur_pos st in
  if i >= st.len then tok "EOF" "" sp sp !st.ncomments
  else
  let (r, e) = select st i in
  let finish (k:string) (txt:string) : ML token =
    st.cur := e;
    tok k txt sp (cur_pos st) !st.ncomments
  in
  let s () : ML string = lexeme st i e in
  match r with
  | REarly k -> finish k ""
  | RTripleBacktick ->
    let name = lexeme st (i + of_int 3) e in
    st.cur := e;
    let pos = cur_pos st in
    blob st [] name pos sp
  | RLang ->
    let name = lexeme st (i + of_int 6) e in
    st.cur := e;
    let pos = cur_pos st in
    use_lang st [] name pos sp
  | RSourceFile -> finish "STRING" (Filepath.basename st.fname)
  | RLine -> finish "INT" (show !st.lnum)
  | RFileLine -> finish "STRING" (Filepath.basename st.fname ^ "(" ^ show !st.lnum ^ ")")
  | RWhite -> st.cur := e; next_token st
  | RNewline -> st.cur := e; new_line st; next_token st
  | RCharLit
  | RCharLitB ->
    let c = unescape st (i + one) in
    let t = finish "CHAR" "" in
    { t with extra = CharLit (to_int c) }
  | RBacktick -> finish "BACKTICK" ""
  | RKwOp (n, k, kop) ->
    let e' = no_comment st i e in
    st.cur := e';
    let rest = lexeme st (i + n) e' in
    let ep = cur_pos st in
    if rest = "" then tok k "" sp ep !st.ncomments
    else tok kop rest sp ep !st.ncomments
  | RSemiSemi -> finish "SEMICOLON_OP" ""
  | RIdent ->
    let id = s () in
    if U.starts_with id Ident.reserved_prefix then
      lex_error st Codes.Fatal_ReservedPrefix
        (Ident.reserved_prefix ^ " is a reserved prefix for an identifier")
        sp (pos_of st e)
    else (match M.try_find keywords id with
          | Some (k, "") -> finish k ""
          | Some (k, t) -> finish k t
          | None -> finish "IDENT" id)
  | RConstructor ->
    let id = s () in
    (match M.try_find constructors id with
     | Some (k, t) -> finish k t
     | None -> finish "NAME" id)
  | RInt -> finish "INT" (clean_number (s ()))
  | RUInt8 ->
    let c = clean_number (s ()) in
    let cv = U.int_of_string c in
    if Prims.(cv < 0 || cv > 255) then
      lex_error st Codes.Fatal_SyntaxError "Out-of-range character literal" sp (pos_of st e)
    else finish "UINT8" c
  | RNumber k -> finish k (clean_number (s ()))
  | RReal -> finish "REAL" (lexeme st i (e - one))
  | RBadNumber ->
    lex_error st Codes.Fatal_SyntaxError ("This is not a valid numeric literal: " ^ s ()) sp (pos_of st e)
  | RCommentStart ->
    let startcol = col_of st i in
    st.cur := e;
    let buf = mk_ref ["(*"] in
    comment st false buf sp startcol;
    next_token st
  | RInFStar -> st.cur := e; next_token st
  | RLineComment ->
    st.cur := e;
    line_comment st (s ());
    next_token st
  | RString ->
    st.cur := e;
    string_lit st [] sp
  | RBacktickIdent -> finish "IDENT" (lexeme st (i + of_int 2) (e - of_int 2))
  | RPipeLeft -> finish "PIPE_LEFT" ""
  | RPipeRight -> finish "PIPE_RIGHT" ""
  | RDotDot -> finish "DOT_DOT" ""
  | ROpToken (k, t) -> finish k t
  | RLt -> finish "OPINFIX0c" "<"
  | RGt ->
    (* sedlex restarts the match after the '>', so the token starts there *)
    let e' = no_comment st (i + one) e in
    st.cur := e';
    tok "OPINFIX0c" (">" ^ lexeme st (i + one) e') (pos_of st (i + one)) (cur_pos st) !st.ncomments
  | ROp k ->
    let e' = no_comment st i e in
    if e' = i then begin
      (* op_infix3 starting with "//": a line comment *)
      line_comment st "";
      next_token st
    end else begin
      st.cur := e';
      tok k (lexeme st i e') sp (cur_pos st) !st.ncomments
    end
  | RUOperator ->
    let id = s () in
    (match M.try_find uoperators id with
     | Some (k, t) -> finish k t
     | None -> finish "OPINFIX4" id)
  | RMixfix k -> finish k (s ())
  | REof -> tok "EOF" "" sp sp !st.ncomments
  | RAny -> lex_error st Codes.Fatal_SyntaxError "unexpected char" sp sp

(* Lex an entire input.  Returns the tokens (ending with EOF or ERROR) and
   the comments, most recent first (as FStarC_Parser_Util.flush_comments). *)
let lex_all (fname:string) (contents:string) (line col:int)
  : ML (list token & list (string & R.range))
= let st = {
    buf = contents;
    len = S.byte_length contents;
    fname = fname;
    cur = mk_ref zero;
    lnum = mk_ref (of_int line);
    bol = mk_ref zero;
    bol_col = mk_ref (of_int col);
    cache_off = mk_ref zero;
    cache_col = mk_ref (of_int col);
    comments = mk_ref [];
    ncomments = mk_ref zero;
  } in
  let rec go (acc:list token) : ML (list token) =
    let t =
      try next_token st
      with LexFail (code, msg, r) ->
        let p = cur_pos st in
        { tok "ERROR" msg p p !st.ncomments with extra = LexError (code, msg, r) }
    in
    if t.kind = "EOF" || t.kind = "ERROR" then List.rev (t :: acc)
    else go (t :: acc)
  in
  let toks = go [] in
  (toks, !st.comments)

open FStar_Parser_Parse
open FStar_Parser_Util

module Option  = BatOption
module String  = BatString
module Hashtbl = BatHashtbl
module Sedlexing = FStar_Sedlexing
module L = Sedlexing
module E = FStar_Errors

let ba_of_string s = Array.init (String.length s) (fun i -> Char.code (String.get s i))
let array_trim_both a n m = Array.sub a n (Array.length a - n - m)
let string_trim_both s n m = BatString.sub s n (String.length s - (n+m))
let trim_both   lexbuf n m = string_trim_both (L.lexeme lexbuf) n m
let utrim_both  lexbuf n m = array_trim_both (L.ulexeme lexbuf) n m
let trim_right  lexbuf n = trim_both lexbuf 0 n
let trim_left   lexbuf n = trim_both lexbuf n 0

let unescape (a:int array) : int =
  match a.(0) with
  | 92 (* \ *) ->
    (match a.(1) with
    | 48  (*0*) -> 0
    | 98  (*b*) -> 8
    | 116 (*t*) -> 9
    | 110 (*n*) -> 10
    | 118 (*v*) -> 11
    | 102 (*f*) -> 12
    | 114 (*r*) -> 13
    | 117 (*u*) ->
      let s = FStar_Parser_Utf8.from_int_array a 2 4 in
      int_of_string ("0x"^s)
    | 120 (*x*) ->
      let s = FStar_Parser_Utf8.from_int_array a 2 2 in
      int_of_string ("0x"^s)
    | c -> c)
  | c -> c

let keywords = Hashtbl.create 0
let constructors = Hashtbl.create 0
let operators = Hashtbl.create 0

let () =
  Hashtbl.add keywords "attributes"    ATTRIBUTES  ;
  Hashtbl.add keywords "noeq"          NOEQUALITY  ;
  Hashtbl.add keywords "unopteq"       UNOPTEQUALITY  ;
  Hashtbl.add keywords "and"           AND         ;
  Hashtbl.add keywords "assert"        ASSERT      ;
  Hashtbl.add keywords "assume"        ASSUME      ;
  Hashtbl.add keywords "begin"         BEGIN       ;
  Hashtbl.add keywords "by"            BY          ;
  Hashtbl.add keywords "calc"          CALC        ;
  Hashtbl.add keywords "class"         CLASS       ;
  Hashtbl.add keywords "default"       DEFAULT     ;
  Hashtbl.add keywords "decreases"     DECREASES   ;
  Hashtbl.add keywords "effect"        EFFECT      ;
  Hashtbl.add keywords "else"          ELSE        ;
  Hashtbl.add keywords "end"           END         ;
  Hashtbl.add keywords "ensures"       ENSURES     ;
  Hashtbl.add keywords "exception"     EXCEPTION   ;
  Hashtbl.add keywords "exists"        EXISTS      ;
  Hashtbl.add keywords "false"         FALSE       ;
  Hashtbl.add keywords "friend"        FRIEND      ;
  Hashtbl.add keywords "forall"        FORALL      ;
  Hashtbl.add keywords "fun"           FUN         ;
  Hashtbl.add keywords "λ"             FUN         ;
  Hashtbl.add keywords "function"      FUNCTION    ;
  Hashtbl.add keywords "if"            IF          ;
  Hashtbl.add keywords "in"            IN          ;
  Hashtbl.add keywords "include"       INCLUDE     ;
  Hashtbl.add keywords "inline"        INLINE      ;
  Hashtbl.add keywords "inline_for_extraction"        INLINE_FOR_EXTRACTION      ;
  Hashtbl.add keywords "instance"      INSTANCE    ;
  Hashtbl.add keywords "irreducible"   IRREDUCIBLE ;
  Hashtbl.add keywords "let"           (LET false) ;
  Hashtbl.add keywords "logic"         LOGIC       ;
  Hashtbl.add keywords "match"         MATCH       ;
  Hashtbl.add keywords "returns"       RETURNS     ;
  Hashtbl.add keywords "module"        MODULE      ;
  Hashtbl.add keywords "new"           NEW         ;
  Hashtbl.add keywords "new_effect"    NEW_EFFECT  ;
  Hashtbl.add keywords "layered_effect"               LAYERED_EFFECT             ;
  Hashtbl.add keywords "polymonadic_bind"             POLYMONADIC_BIND           ;
  Hashtbl.add keywords "polymonadic_subcomp"          POLYMONADIC_SUBCOMP        ;
  Hashtbl.add keywords "noextract"     NOEXTRACT   ;
  Hashtbl.add keywords "of"            OF          ;
  Hashtbl.add keywords "open"          OPEN        ;
  Hashtbl.add keywords "opaque"        OPAQUE      ;
  Hashtbl.add keywords "private"       PRIVATE     ;
  Hashtbl.add keywords "range_of"      RANGE_OF    ;
  Hashtbl.add keywords "rec"           REC         ;
  Hashtbl.add keywords "reifiable"     REIFIABLE   ;
  Hashtbl.add keywords "reify"         REIFY       ;
  Hashtbl.add keywords "reflectable"   REFLECTABLE ;
  Hashtbl.add keywords "requires"      REQUIRES    ;
  Hashtbl.add keywords "set_range_of"  SET_RANGE_OF;
  Hashtbl.add keywords "sub_effect"    SUB_EFFECT  ;
  Hashtbl.add keywords "synth"         SYNTH       ;
  Hashtbl.add keywords "then"          THEN        ;
  Hashtbl.add keywords "total"         TOTAL       ;
  Hashtbl.add keywords "true"          TRUE        ;
  Hashtbl.add keywords "try"           TRY         ;
  Hashtbl.add keywords "type"          TYPE        ;
  Hashtbl.add keywords "unfold"        UNFOLD      ;
  Hashtbl.add keywords "unfoldable"    UNFOLDABLE  ;
  Hashtbl.add keywords "val"           VAL         ;
  Hashtbl.add keywords "when"          WHEN        ;
  Hashtbl.add keywords "with"          WITH        ;
  Hashtbl.add keywords "_"             UNDERSCORE  ;
  Hashtbl.add keywords "α"             (TVAR "a")  ;
  Hashtbl.add keywords "β"             (TVAR "b")  ;
  Hashtbl.add keywords "γ"             (TVAR "c")  ;
  Hashtbl.add keywords "δ"             (TVAR "d")  ;
  Hashtbl.add keywords "ε"             (TVAR "e")  ;
  Hashtbl.add keywords "φ"             (TVAR "f")  ;
  Hashtbl.add keywords "χ"             (TVAR "g")  ;
  Hashtbl.add keywords "η"             (TVAR "h")  ;
  Hashtbl.add keywords "ι"             (TVAR "i")  ;
  Hashtbl.add keywords "κ"             (TVAR "k")  ;
  Hashtbl.add keywords "μ"             (TVAR "m")  ;
  Hashtbl.add keywords "ν"             (TVAR "n")  ;
  Hashtbl.add keywords "π"             (TVAR "p")  ;
  Hashtbl.add keywords "θ"             (TVAR "q")  ;
  Hashtbl.add keywords "ρ"             (TVAR "r")  ;
  Hashtbl.add keywords "σ"             (TVAR "s")  ;
  Hashtbl.add keywords "τ"             (TVAR "t")  ;
  Hashtbl.add keywords "ψ"             (TVAR "u")  ;
  Hashtbl.add keywords "ω"             (TVAR "w")  ;
  Hashtbl.add keywords "ξ"             (TVAR "x")  ;
  Hashtbl.add keywords "ζ"             (TVAR "z")  ;
  Hashtbl.add constructors "ℕ"         (IDENT "nat");
  Hashtbl.add constructors "ℤ"         (IDENT "int");
  Hashtbl.add constructors "𝔹"         (IDENT "bool");
  let l =
  ["~", TILDE "~";
   "-", MINUS;
   "/\\", CONJUNCTION;
   "\\/", DISJUNCTION;
   "<:", SUBTYPE;
   "<@", SUBKIND;
   "(|", LENS_PAREN_LEFT;
   "|)", LENS_PAREN_RIGHT;
   "#", HASH;
   "u#", UNIV_HASH;
   "&", AMP;
   "()", LPAREN_RPAREN;
   "(", LPAREN;
   ")", RPAREN;
   ",", COMMA;
   "~>", SQUIGGLY_RARROW;
   "->", RARROW;
   "<--", LONG_LEFT_ARROW;
   "<-", LARROW;
   "<==>", IFF;
   "==>", IMPLIES;
   ".", DOT;
   "?.", QMARK_DOT;
   "?", QMARK;
   ".[", DOT_LBRACK;
   ".(|", DOT_LENS_PAREN_LEFT;
   ".(", DOT_LPAREN;
   ".[|", DOT_LBRACK_BAR;
   "{:pattern", LBRACE_COLON_PATTERN;
   "{:well-founded", LBRACE_COLON_WELL_FOUNDED;
   ":", COLON;
   "::", COLON_COLON;
   ":=", COLON_EQUALS;
   ";;", SEMICOLON_SEMICOLON;
   ";", SEMICOLON;
   "=", EQUALS;
   "%[", PERCENT_LBRACK;
   "!{", BANG_LBRACE;
   "[@@@", LBRACK_AT_AT_AT;
   "[@@", LBRACK_AT_AT;
   "[@", LBRACK_AT;
   "[", LBRACK;
   "[|", LBRACK_BAR;
   "{|", LBRACE_BAR;
   "|>", PIPE_RIGHT;
   "]", RBRACK;
   "|]", BAR_RBRACK;
   "|}", BAR_RBRACE;
   "{", LBRACE;
   "|", BAR;
   "}", RBRACE;
   "$", DOLLAR;
     (* New Unicode equivalents *)
   "∀", FORALL;
   "∃", EXISTS;
   "⊤", NAME "True";
   "⊥", NAME "False";
   "⟹", IMPLIES;
   "⟺", IFF;
   "→", RARROW;
   "←", LARROW;
   "⟵", LONG_LEFT_ARROW;
   "↝", SQUIGGLY_RARROW;
   "≔", COLON_EQUALS;
   "∧", CONJUNCTION;
   "∨", DISJUNCTION;
   "¬", TILDE "~";
   "⸬", COLON_COLON;
   "▹", PIPE_RIGHT;
   "÷", OPINFIX3 "÷";
   "‖", OPINFIX0a "||";
   "×", IDENT "op_Multiply";
   "∗", OPINFIX3 "*";
   "⇒", OPINFIX0c "=>";
   "≥", OPINFIX0c ">=";
   "≤", OPINFIX0c "<=";
   "≠", OPINFIX0c "<>";
   "≪", OPINFIX0c "<<";
   "◃", OPINFIX0c "<|";
   "±", OPPREFIX "±";
   "∁", OPPREFIX "∁";
   "∂", OPPREFIX "∂";
   "√", OPPREFIX "√";
    ] in
   List.iter (fun (k,v) -> Hashtbl.add operators k v) l

let current_range lexbuf =
    FStar_Parser_Util.mksyn_range (fst (L.range lexbuf)) (snd (L.range lexbuf))

let fail lexbuf (e, msg) =
     let m = current_range lexbuf in
     E.raise_error (e, msg) m

type delimiters = { angle:int ref; paren:int ref; }
let n_typ_apps = ref 0

(* ADL: unicode identifiers won't work with --fs_typ_app
   Since this is only used for bootstrapping I am not going to bother fixing this *)
let is_typ_app lexbuf =
  if not (FStar_Options.fs_typ_app (L.source_file lexbuf)) then false
  else
   try
    let char_ok = function
      | '(' | ')' | '<' | '>' | '*' | '-' | '\'' | '_' | ',' | '.' | ' ' | '\t' -> true
      | c when c >= 'A' && c <= 'Z' -> true
      | c when c >= 'a' && c <= 'z' -> true
      | c when c >= '0' && c <= '9' -> true
      | _ -> false in
    let balanced (contents:string) pos =
      if contents.[pos] <> '<' then (fail lexbuf (E.Fatal_SyntaxError, "Unexpected position in is_typ_lapp"));
      let d = {angle=ref 1; paren=ref 0} in
      let upd i = match contents.[i] with
        | '(' -> incr d.paren
        | ')' -> decr d.paren
        | '<' -> incr d.angle
        | '>' when contents.[i-1] <> '-' -> decr d.angle
        | _ -> () in
      let ok () = !(d.angle) >= 0 && !(d.paren) >= 0 in
      let rec aux i =
        if !(d.angle)=0 && !(d.paren)=0 then true
        else if i >= String.length contents || not (ok ()) || (not (char_ok (contents.[i]))) || FStar_Util.(starts_with (substring_from contents (Z.of_int i)) "then") then false
        else (upd i; aux (i + 1))
      in aux (pos + 1)
    in
    let res = balanced (L.lookahead lexbuf (L.get_cur lexbuf - 1)) 0 in
    if res then incr n_typ_apps; res
   with e -> Printf.printf "Resolving typ_app<...> syntax failed.\n"; false

let is_typ_app_gt () =
  if !n_typ_apps > 0
  then (decr n_typ_apps; true)
  else false

let rec mknewline n lexbuf =
  if n = 0 then ()
  else (L.new_line lexbuf; mknewline (n-1) lexbuf)

let clean_number x = String.strip ~chars:"uzyslLUnIN" x

(* Try to trim each line of [comment] by the ammount of space
    on the first line of the comment if possible *)
(* TODO : apply this to FSDOC too *)
let maybe_trim_lines start_column comment =
  if start_column = 0 then comment
  else
    let comment_lines = String.split_on_char '\n' comment in
    let ensures_empty_prefix k s =
      let j = min k (String.length s - 1) in
      let rec aux i = if i > j then k else if s.[i] <> ' ' then i else aux (i+1) in
      aux 0 in
    let trim_width = List.fold_left ensures_empty_prefix start_column comment_lines in
    String.concat "\n" (List.map (fun s -> String.tail s trim_width) comment_lines)

let comment_buffer = Buffer.create 128

let start_comment lexbuf =
  Buffer.add_string comment_buffer "(*" ;
  (false, comment_buffer, fst (L.range lexbuf))

let terminate_comment buffer startpos lexbuf =
  let endpos = snd (L.range lexbuf) in
  Buffer.add_string buffer "*)" ;
  let comment = Buffer.contents buffer in
  let comment = maybe_trim_lines (startpos.Lexing.pos_cnum - startpos.Lexing.pos_bol) comment in
  Buffer.clear buffer;
  add_comment (comment, FStar_Parser_Util.mksyn_range startpos endpos)

let push_one_line_comment pre lexbuf =
  let startpos, endpos = L.range lexbuf in
  assert (startpos.Lexing.pos_lnum = endpos.Lexing.pos_lnum);
  add_comment (pre ^ L.lexeme lexbuf, FStar_Parser_Util.mksyn_range startpos endpos)

(** Unicode class definitions
  Auto-generated from http:/ /www.unicode.org/Public/8.0.0/ucd/UnicodeData.txt **)
(** Ll **)
let u_lower = [%sedlex.regexp? ll]
(** Lu *)
let u_upper = [%sedlex.regexp? lu]
(** Lo *)
let u_other = [%sedlex.regexp? lo]
(** Lm *)
let u_modifier = [%sedlex.regexp? lm]
(** Lt *)
let u_title = [%sedlex.regexp? lt]
(** Zs *)
let u_space = [%sedlex.regexp? zs]
(** These are not unicode spaces but we accept as whitespace in F* source (e.g. tab and BOM) *)
let u_space_extra = [%sedlex.regexp? '\t' | '\x0B' | '\x0C' | '\xA0' | 0xfeff]
(** Zl and Zp *)
let u_line_sep = [%sedlex.regexp? zl]
let u_par_sep = [%sedlex.regexp? zp]
(** Sm math symbols *)
let u_math = [%sedlex.regexp? sm]
let u_math_ascii = [%sedlex.regexp? 0x002b | 0x003c .. 0x003e | 0x007c | 0x007e]
let u_math_nonascii = [%sedlex.regexp? Sub(u_math, u_math_ascii)]
(** Sc currency *)
let u_currency = [%sedlex.regexp? sc]
(** Sk *)
let u_modifier_symbol = [%sedlex.regexp? sk]
(** So *)
let u_other_symbol = [%sedlex.regexp? so]
(** Nd *)
let u_decimal_digit = [%sedlex.regexp? nd]
(** Nl *)
let u_digit_letter = [%sedlex.regexp? nl]
(** No *)
let u_other_digit = [%sedlex.regexp? no]
(** Pd *)
let u_punct_hyphen = [%sedlex.regexp? pd]
(** Ps *)
let u_punct_obra = [%sedlex.regexp? ps]
(** Pe *)
let u_punct_cbra = [%sedlex.regexp? pe]
(** Pi *)
let u_punct_oquot = [%sedlex.regexp? pi]
(** Pf *)
let u_punct_cquot = [%sedlex.regexp? pf]
(** Pc *)
let u_punct_connect = [%sedlex.regexp? pc]
(** Po *)
let u_punct_other = [%sedlex.regexp? po]
(** Mn *)
let u_mod_nospace = [%sedlex.regexp? mn]
(** Mc *)
let u_mod = [%sedlex.regexp? mc]
(** Me *)
let u_mod_enclose = [%sedlex.regexp? me]
(** Cc *)
let u_ascii_control = [%sedlex.regexp? cc]
(** Cf *)
let u_format_control = [%sedlex.regexp? cf]
(** Co *)
let u_private_use = [%sedlex.regexp? co]
(** Cs *)
let u_surrogate = [%sedlex.regexp? cs]

(* -------------------------------------------------------------------- *)
let lower  = [%sedlex.regexp? u_lower]
let upper  = [%sedlex.regexp? u_upper | u_title]
let letter = [%sedlex.regexp? u_lower | u_upper | u_other | u_modifier]
let digit  = [%sedlex.regexp? '0'..'9']
let hex    = [%sedlex.regexp? '0'..'9' | 'A'..'F' | 'a'..'f']

(* -------------------------------------------------------------------- *)
let anywhite  = [%sedlex.regexp? u_space | u_space_extra]
let newline   = [%sedlex.regexp? "\r\n" | 10 | 13 | 0x2028 | 0x2029]

(* -------------------------------------------------------------------- *)
let op_char = [%sedlex.regexp? Chars "!$%&*+-./<=?^|~:"]
let ignored_op_char = [%sedlex.regexp? Chars ".$"]

(* op_token must be splt into seperate regular expressions to prevent
   compliation from hanging *)
let op_token_1 = [%sedlex.regexp? "~" | "-" | "/\\" | "\\/" | "<:" | "<@" | "(|" | "|)" | "#" ]
let op_token_2 = [%sedlex.regexp? "u#" | "&" | "()" | "(" | ")" | "," | "~>" | "->" | "<--" ]
let op_token_3 = [%sedlex.regexp? "<-" | "<==>" | "==>" | "." | "?." | "?" | ".[|" | ".[" | ".(|" | ".(" ]
let op_token_4 = [%sedlex.regexp? "$" | "{:pattern" | "{:well-founded" | ":" | "::" | ":=" | ";;" | ";" | "=" | "%[" ]
let op_token_5 = [%sedlex.regexp? "!{" | "[@@@" | "[@@" | "[@" | "[|" | "{|" | "[" | "|>" | "]" | "|]" | "|}" | "{" | "|" | "}" ]

(* -------------------------------------------------------------------- *)
let xinteger =
  [%sedlex.regexp?
  (  '0', ('x'| 'X'), Plus hex
   | '0', ('o'| 'O'), Plus ('0' .. '7')
   | '0', ('b'| 'B'), Plus ('0' .. '1') )]
let integer = [%sedlex.regexp? Plus digit]
let any_integer = [%sedlex.regexp? xinteger | integer]
let unsigned = [%sedlex.regexp? Chars "uU"]
let int8 = [%sedlex.regexp? any_integer, 'y']
let uint8 = [%sedlex.regexp? any_integer, unsigned, 'y']
let int16 = [%sedlex.regexp? any_integer, 's']
let uint16 = [%sedlex.regexp? any_integer, unsigned, 's']
let int32 = [%sedlex.regexp? any_integer, 'l']
let uint32 = [%sedlex.regexp? any_integer, unsigned, 'l']
let int64 = [%sedlex.regexp? any_integer, 'L']
let uint64 = [%sedlex.regexp? any_integer, unsigned, 'L']
let char8 = [%sedlex.regexp? any_integer, 'z']

let floatp     = [%sedlex.regexp? Plus digit, '.', Star digit]
let floate     = [%sedlex.regexp? Plus digit, Opt ('.', Star digit), Chars "eE", Opt (Chars "+-"), Plus digit]
let real       = [%sedlex.regexp? floatp, 'R']
let ieee64     = [%sedlex.regexp? floatp | floate]
let xieee64    = [%sedlex.regexp? xinteger, 'L', 'F']
let range      = [%sedlex.regexp? Plus digit, '.', '.', Plus digit]

let op_prefix  = [%sedlex.regexp? Chars "!~?"]
let op_infix0a = [%sedlex.regexp? Chars "|"] (* left *)
let op_infix0b = [%sedlex.regexp? Chars "&"] (* left *)
let op_infix0c = [%sedlex.regexp? Chars "=<>"] (* left *)
let op_infix0c_nogt = [%sedlex.regexp? Chars "=<"] (* left *)
let op_infix0d = [%sedlex.regexp? Chars "$"] (* left *)

let op_infix0  = [%sedlex.regexp? op_infix0a | op_infix0b | op_infix0c | op_infix0d]
let op_infix1  = [%sedlex.regexp? Chars "@^"] (* right *)
let op_infix2  = [%sedlex.regexp? Chars "+-"] (* left *)
let op_infix3  = [%sedlex.regexp? Chars "*/%"] (* left *)
let symbolchar = [%sedlex.regexp? op_prefix | op_infix0 | op_infix1 | op_infix2 | op_infix3 | Chars ".:"]
let uoperator  = [%sedlex.regexp? u_math_nonascii]

(* -------------------------------------------------------------------- *)
let escape_char = [%sedlex.regexp? '\\', (Chars "\\\"'bfntrv0" | "x", hex, hex | "u", hex, hex, hex, hex)]
let char        = [%sedlex.regexp? Compl '\\' | escape_char]

(* -------------------------------------------------------------------- *)
let constructor_start_char = [%sedlex.regexp? upper]
let ident_start_char       = [%sedlex.regexp? lower  | '_']
let ident_char             = [%sedlex.regexp? letter | digit | '\'' | '_']
let tvar_char              = [%sedlex.regexp? letter | digit | '\'' | '_']

let constructor = [%sedlex.regexp? constructor_start_char, Star ident_char]
let ident       = [%sedlex.regexp? ident_start_char, Star ident_char]
let tvar        = [%sedlex.regexp? '\'', (ident_start_char | constructor_start_char), Star tvar_char]

let rec token lexbuf =
match%sedlex lexbuf with
 | "%splice" -> SPLICE
 | "`%" -> BACKTICK_PERC
 | "`#" -> BACKTICK_HASH
 | "`@" -> BACKTICK_AT
 | "quote" -> QUOTE
 | "#light" -> FStar_Options.add_light_off_file (L.source_file lexbuf); PRAGMALIGHT
 | "#set-options" -> PRAGMA_SET_OPTIONS
 | "#reset-options" -> PRAGMA_RESET_OPTIONS
 | "#push-options" -> PRAGMA_PUSH_OPTIONS
 | "#pop-options" -> PRAGMA_POP_OPTIONS
 | "#restart-solver" -> PRAGMA_RESTART_SOLVER
 | "__SOURCE_FILE__" -> STRING (L.source_file lexbuf)
 | "__LINE__" -> INT (string_of_int (L.current_line lexbuf), false)

 | Plus anywhite -> token lexbuf
 | newline -> L.new_line lexbuf; token lexbuf

 (* Must appear before tvar to avoid 'a <-> 'a' conflict *)
 | ('\'', char, '\'') -> CHAR (unescape (utrim_both lexbuf 1 1))
 | ('\'', char, '\'', 'B') -> CHAR (unescape (utrim_both lexbuf 1 2))
 | '`' -> BACKTICK

 | ident -> let id = L.lexeme lexbuf in
   if FStar_Util.starts_with id FStar_Ident.reserved_prefix
   then FStar_Errors.raise_error
                    (FStar_Errors.Fatal_ReservedPrefix,
                     FStar_Ident.reserved_prefix  ^ " is a reserved prefix for an identifier")
                    (current_range lexbuf);
   Hashtbl.find_option keywords id |> Option.default (IDENT id)
 | constructor -> let id = L.lexeme lexbuf in
   Hashtbl.find_option constructors id |> Option.default (NAME id)

 | tvar -> TVAR (L.lexeme lexbuf)
 | (integer | xinteger) -> INT (clean_number (L.lexeme lexbuf), false)
 | (uint8 | char8) ->
   let c = clean_number (L.lexeme lexbuf) in
   let cv = int_of_string c in
   if cv < 0 || cv > 255 then fail lexbuf (E.Fatal_SyntaxError, "Out-of-range character literal")
   else UINT8 (c)
 | int8 -> INT8 (clean_number (L.lexeme lexbuf), false)
 | uint16 -> UINT16 (clean_number (L.lexeme lexbuf))
 | int16 -> INT16 (clean_number (L.lexeme lexbuf), false)
 | uint32 -> UINT32 (clean_number (L.lexeme lexbuf))
 | int32 -> INT32 (clean_number (L.lexeme lexbuf), false)
 | uint64 -> UINT64 (clean_number (L.lexeme lexbuf))
 | int64 -> INT64 (clean_number (L.lexeme lexbuf), false)
 | range -> RANGE (L.lexeme lexbuf)
 | real -> REAL(trim_right lexbuf 1)
 | (ieee64 | xieee64) -> IEEE64 (float_of_string (L.lexeme lexbuf))
 | (integer | xinteger | ieee64 | xieee64), Plus ident_char ->
   fail lexbuf (E.Fatal_SyntaxError, "This is not a valid numeric literal: " ^ L.lexeme lexbuf)

 | "(*" ->
   let inner, buffer, startpos = start_comment lexbuf in
   comment inner buffer startpos lexbuf

 | "// IN F*:" -> token lexbuf
 | "//" ->
     (* Only match on "//" to allow the longest-match rule to catch IN F*. This
      * creates a lexing conflict with op_infix3 which is caught below. *)
     one_line_comment (L.lexeme lexbuf) lexbuf

 | '"' -> string (Buffer.create 0) lexbuf.Sedlexing.start_p lexbuf

 | '`', '`', (Plus (Compl ('`' | 10 | 13 | 0x2028 | 0x2029) | '`', Compl ('`' | 10 | 13 | 0x2028 | 0x2029))), '`', '`' ->
   IDENT (trim_both lexbuf 2 2)

 | op_token_1
 | op_token_2
 | op_token_3
 | op_token_4
 | op_token_5 -> L.lexeme lexbuf |> Hashtbl.find operators

 | "<"       -> if is_typ_app lexbuf then TYP_APP_LESS else OPINFIX0c("<")
 | ">"       -> if is_typ_app_gt () then TYP_APP_GREATER else symbolchar_parser lexbuf

 (* Operators. *)
 | op_prefix,  Star symbolchar -> OPPREFIX (L.lexeme lexbuf)
 | op_infix0a, Star symbolchar -> OPINFIX0a (L.lexeme lexbuf)
 | op_infix0b, Star symbolchar -> OPINFIX0b (L.lexeme lexbuf)
 | op_infix0c_nogt, Star symbolchar -> OPINFIX0c (L.lexeme lexbuf)
 | op_infix0d, Star symbolchar -> OPINFIX0d (L.lexeme lexbuf)
 | op_infix1,  Star symbolchar -> OPINFIX1 (L.lexeme lexbuf)
 | op_infix2,  Star symbolchar -> OPINFIX2 (L.lexeme lexbuf)
 | "**"     ,  Star symbolchar -> OPINFIX4 (L.lexeme lexbuf)

 (* Unicode Operators *)
 | uoperator -> let id = L.lexeme lexbuf in
   Hashtbl.find_option operators id |> Option.default (OPINFIX4 id)

 | op_infix3, Star symbolchar ->
     let l = L.lexeme lexbuf in
     if String.length l >= 2 && String.sub l 0 2 = "//" then
       one_line_comment l lexbuf
     else
        OPINFIX3 l
 | ".[]<-"                 -> OP_MIXFIX_ASSIGNMENT (L.lexeme lexbuf)
 | ".()<-"                 -> OP_MIXFIX_ASSIGNMENT (L.lexeme lexbuf)
 | ".(||)<-"                -> OP_MIXFIX_ASSIGNMENT (L.lexeme lexbuf)
 | ".[||]<-"                 -> OP_MIXFIX_ASSIGNMENT (L.lexeme lexbuf)
 | ".[]"                  -> OP_MIXFIX_ACCESS (L.lexeme lexbuf)
 | ".()"                  -> OP_MIXFIX_ACCESS (L.lexeme lexbuf)
 | ".(||)"                 -> OP_MIXFIX_ACCESS (L.lexeme lexbuf)
 | ".[||]"                  -> OP_MIXFIX_ACCESS (L.lexeme lexbuf)

 | eof -> EOF
 | _ -> fail lexbuf (E.Fatal_SyntaxError, "unexpected char")

and one_line_comment pre lexbuf =
match%sedlex lexbuf with
 | Star (Compl (10 | 13 | 0x2028 | 0x2029)) -> push_one_line_comment pre lexbuf; token lexbuf
 | _ -> assert false

and symbolchar_parser lexbuf =
match%sedlex lexbuf with
 | Star symbolchar -> OPINFIX0c (">" ^  L.lexeme lexbuf)
 | _ -> assert false

and string buffer start_pos lexbuf =
match%sedlex lexbuf with
 | '\\', newline, Star anywhite -> L.new_line lexbuf; string buffer start_pos lexbuf
 | newline ->
   Buffer.add_string buffer (L.lexeme lexbuf);
   L.new_line lexbuf; string buffer start_pos lexbuf
 | escape_char ->
   Buffer.add_string buffer (BatUTF8.init 1 (fun _ -> unescape (L.ulexeme lexbuf) |> BatUChar.chr));
   string buffer start_pos lexbuf
 | '"' ->
   (* position info must be set since the start of the string *)
   lexbuf.Sedlexing.start_p <- start_pos;
   STRING (Buffer.contents buffer)
 | '"', 'B' ->
   (* as above *)
   lexbuf.Sedlexing.start_p <- start_pos;
   BYTEARRAY (ba_of_string (Buffer.contents buffer))
 | eof -> fail lexbuf (E.Fatal_SyntaxError, "unterminated string")
 | any ->
  Buffer.add_string buffer (L.lexeme lexbuf);
  string buffer start_pos lexbuf
 | _ -> assert false

and comment inner buffer startpos lexbuf =
match%sedlex lexbuf with
 | "(*" ->
   Buffer.add_string buffer "(*" ;
   let _ = comment true buffer startpos lexbuf in
   comment inner buffer startpos lexbuf
 | newline ->
   L.new_line lexbuf;
   Buffer.add_string buffer (L.lexeme lexbuf);
   comment inner buffer startpos lexbuf
 | "*)" ->
   terminate_comment buffer startpos lexbuf;
   if inner then EOF else token lexbuf
 | eof ->
   terminate_comment buffer startpos lexbuf; EOF
 | any ->
   Buffer.add_string buffer (L.lexeme lexbuf);
   comment inner buffer startpos lexbuf
 | _ -> assert false

and ignore_endline lexbuf =
match%sedlex lexbuf with
 | Star ' ', newline -> token lexbuf
 | _ -> assert false

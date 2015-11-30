{
  open FStar_Parser_Parse
  open Lexing

  module Option  = BatOption
  module String  = BatString
  module Hashtbl = BatHashtbl

  module L : sig
    include module type of struct include Lexing end

    val range : lexbuf -> position * position
  end = struct
    include Lexing

    let range (lexbuf : lexbuf) =
      (lexeme_start_p lexbuf, lexeme_end_p lexbuf)
  end

  let string_trim_both s n m = FStar_Util.substring s n (String.length s - (n+m))
  let trim_both   lexbuf n m = string_trim_both (L.lexeme lexbuf) n m
  let trim_right  lexbuf n = trim_both lexbuf 0 n
  let trim_left   lexbuf n = trim_both lexbuf n 0

  let char_of_ec = function
    | '\'' -> '\''
    | '\"' -> '"'
    | '\\' -> '\\'
    | 'n'  -> '\n'
    | 't'  -> '\t'
    | 'b'  -> '\b'
    | 'r'  -> '\r'
    | _    -> assert false

  let keywords = Hashtbl.create 0

  let () =
    Hashtbl.add keywords "and"           AND         ;
    Hashtbl.add keywords "as"            AS          ;
    Hashtbl.add keywords "assert"        ASSERT      ;
    Hashtbl.add keywords "assume"        ASSUME      ;
    Hashtbl.add keywords "begin"         BEGIN       ;
    Hashtbl.add keywords "default"       DEFAULT     ;
    Hashtbl.add keywords "effect"        EFFECT      ;
    Hashtbl.add keywords "else"          ELSE        ;
    Hashtbl.add keywords "end"           END         ;
    Hashtbl.add keywords "ensures"       ENSURES     ;
    Hashtbl.add keywords "exception"     EXCEPTION   ;
    Hashtbl.add keywords "exists"        EXISTS      ;
    Hashtbl.add keywords "false"         FALSE       ;
    Hashtbl.add keywords "finally"       FINALLY     ;
    Hashtbl.add keywords "for"           FOR         ;
    Hashtbl.add keywords "forall"        FORALL      ;
    Hashtbl.add keywords "fun"           FUN         ;
    Hashtbl.add keywords "function"      FUNCTION    ;
    Hashtbl.add keywords "if"            IF          ;
    Hashtbl.add keywords "kind"          KIND        ;
    Hashtbl.add keywords "in"            IN          ;
    Hashtbl.add keywords "lazy"          LAZY        ;
    Hashtbl.add keywords "let"           (LET false) ;
    Hashtbl.add keywords "logic"         LOGIC       ;
    Hashtbl.add keywords "match"         MATCH       ;
    Hashtbl.add keywords "module"        MODULE      ;
    Hashtbl.add keywords "new_effect"    NEW_EFFECT  ;
    Hashtbl.add keywords "of"            OF          ;
    Hashtbl.add keywords "open"          OPEN        ;
    Hashtbl.add keywords "or"            OR          ;
    Hashtbl.add keywords "opaque"        OPAQUE      ;
    Hashtbl.add keywords "private"       PRIVATE     ;
    Hashtbl.add keywords "public"        PUBLIC      ;
    Hashtbl.add keywords "rec"           REC         ;
    Hashtbl.add keywords "requires"      REQUIRES    ;
    Hashtbl.add keywords "sub_effect"    SUB_EFFECT  ;
    Hashtbl.add keywords "then"          THEN        ;
    Hashtbl.add keywords "to"            TO          ;
    Hashtbl.add keywords "total"         TOTAL       ;
    Hashtbl.add keywords "true"          TRUE        ;
    Hashtbl.add keywords "try"           TRY         ;
    Hashtbl.add keywords "type"          TYPE        ;
    Hashtbl.add keywords "val"           VAL         ;
    Hashtbl.add keywords "when"          WHEN        ;
    Hashtbl.add keywords "with"          WITH        ;
    Hashtbl.add keywords "_"             UNDERSCORE

  type delimiters = { angle:int ref; paren:int ref; }

  let ba_of_string s = Array.init (String.length s) (String.get s)
  let n_typ_apps = FStar_Util.mk_ref 0
  let is_typ_app lexbuf =
  if not !FStar_Options.fs_typ_app then false
  else try
   let char_ok = function
     | '(' | ')' | '<' | '>' | '*' | '-' | '\'' | '_' | ',' | '.' | ' ' | '\t' -> true
     | c when c >= 'A' && c <= 'Z' -> true
     | c when c >= 'a' && c <= 'z' -> true
     | c when c >= '0' && c <= '9' -> true
     | _ -> false in
   let balanced (contents:string) pos =
    if FStar_Util.char_at contents pos <> '<' then
      (failwith  "Unexpected position in is_typ_lapp");
    let d = {angle=ref 1; paren=ref 0} in
    let upd i = match FStar_Util.char_at contents i with
      | '(' -> incr d.paren | ')' -> decr d.paren
      | '<' -> incr d.angle | '>' -> decr d.angle
      | _ -> () in
    let ok () = !(d.angle) >= 0 && !(d.paren) >= 0 in
    let rec aux i =
      if !(d.angle)=0 && !(d.paren)=0 then true
      else if i >= String.length contents || not (ok ()) || (not (char_ok (FStar_Util.char_at contents i))) || (FStar_Util.starts_with (FStar_Util.substring_from contents i) "then") then false
      else (upd i; aux (i + 1)) in
      aux (pos + 1) in
   let rest = String.sub lexbuf.lex_buffer lexbuf.lex_last_pos (lexbuf.lex_buffer_len - lexbuf.lex_last_pos) in
   if not (String.contains rest '\n') then (lexbuf.refill_buff lexbuf);
   let lookahead = String.sub lexbuf.lex_buffer (lexbuf.lex_last_pos - 1) (lexbuf.lex_buffer_len - lexbuf.lex_last_pos + 1) in
   let res = balanced lookahead 0 in
   if res then FStar_Util.incr n_typ_apps;
   (*Printf.printf "TYP_APP %s: %s\n" lookahead (if res then "YES" else "NO");*)
   res
  with e -> Printf.printf "Resolving typ_app<...> syntax failed.\n"; false

  let is_typ_app_gt () =
    if !n_typ_apps > 0
    then (FStar_Util.decr n_typ_apps; true)
    else false

  let lc = FStar_Util.mk_ref 1
  let rec mknewline n lexbuf =
    if n > 0 then (L.new_line lexbuf; FStar_Util.incr lc; mknewline (n-1) lexbuf)

 let clean_number x = String.strip ~chars:"uyslLUnIN" x
}

(* -------------------------------------------------------------------- *)
let lower  = ['a'-'z']
let upper  = ['A'-'Z']
let letter = upper | lower
let digit  = ['0'-'9']
let hex    = ['0'-'9'] | ['A'-'F'] | ['a'-'f']

(* -------------------------------------------------------------------- *)
let truewhite = [' ']
let offwhite  = ['\t']
let anywhite  = truewhite | offwhite
let newline   = ('\n' | '\r' '\n')

(* -------------------------------------------------------------------- *)
let op_char = '!'|'$'|'%'|'&'|'*'|'+'|'-'|'.'|'/'|'<'|'='|'?'|'^'|'|'|'~'|':'
let ignored_op_char = '.' | '$'

(* -------------------------------------------------------------------- *)
let xinteger =
  (  '0' ('x'| 'X')  hex +
   | '0' ('o'| 'O')  (['0'-'7']) +
   | '0' ('b'| 'B')  (['0'-'1']) + )

let integer    = digit+
let int8       = integer 'y'
let uint8      = (xinteger | integer) 'u' 'y'
let int16      = integer 's'
let uint16     = (xinteger | integer) 'u' 's'
let int        = integer
let int32      = integer 'l'
let uint32     = (xinteger | integer) 'u'
let uint32l    = (xinteger | integer) 'u' 'l'
let nativeint  = (xinteger | integer) 'n'
let unativeint = (xinteger | integer) 'u' 'n'
let int64      = (xinteger | integer) 'L'
let uint64     = (xinteger | integer) ('u' | 'U') 'L'
let xint8      = xinteger 'y'
let xint16     = xinteger 's'
let xint       = xinteger
let xint32     = xinteger 'l'
let floatp     = digit+ '.' digit*
let floate     = digit+ ('.' digit* )? ('e'| 'E') ['+' '-']? digit+
let float      = floatp | floate
let bigint     = integer 'I'
let bignum     = integer 'N'
let ieee64     = float
let ieee32     = float ('f' | 'F')
let decimal    = (float | integer) ('m' | 'M')
let xieee32    = xinteger 'l' 'f'
let xieee64    = xinteger 'L' 'F'

(* -------------------------------------------------------------------- *)
let escape_char = ('\\' ( '\\' | "\"" | '\'' | 'n' | 't' | 'b' | 'r'))
let char        = [^'\\''\n''\r''\t''\b'] | escape_char
let custom_op_char = '&'|'@'|'+'|'-'|'/'|'<'|'='|'|'|'!'|'^'|'?'
let custom_op = custom_op_char (custom_op_char | '>' | '*' | '%')*

(* -------------------------------------------------------------------- *)
let constructor_start_char = upper
let ident_start_char       = lower  | '_'
let ident_char             = letter | digit  | '\'' | '_'
let tvar_char              = letter | digit | '\'' | '_'

let constructor = constructor_start_char ident_char*
let ident       = ident_start_char ident_char*
let tvar        = '\'' (ident_start_char | constructor_start_char) tvar_char*

rule token = parse
 | "\xef\xbb\xbf"   (* UTF-8 byte order mark, some compiler files have them *)
     {token lexbuf}
 | "#light"
     { PRAGMALIGHT }
 | "#set-options"
     { PRAGMA_SET_OPTIONS }
 | "#reset-options"
     { PRAGMA_RESET_OPTIONS }
 | '#' ' ' (digit)*
     { let n = int_of_string (trim_left lexbuf 2) in
       mknewline (n - !lc) lexbuf;
       cpp_filename lexbuf }
 | "__SOURCE_FILE__" {STRING (ba_of_string lexbuf.lex_curr_p.pos_fname)}
 | "__LINE__"  {INT (string_of_int !lc, false)}

 (* Must appear before tvar to avoid 'a <-> 'a' conflict *)
 | '\'' (char as c) '\''
 | '\'' (char as c) '\'' 'B'
     { let c =
         match c.[0] with
         | '\\' -> char_of_ec c.[1]
         | _    -> c.[0]
     in CHAR c }
 | ident as id
     { id |> Hashtbl.find_option keywords |> Option.default (IDENT id) }
 | constructor as id
     { NAME id }
 | tvar as id
     { TVAR id }
 | uint8 as x
     { UINT8 (char_of_int (int_of_string (clean_number x))) }
 | (int8 | xint8) as x
     { INT8 (char_of_int (int_of_string (clean_number x)), false) }
 | (uint16 | int16 | xint16) as x
     { INT16 (int_of_string (clean_number x), false) }
 | (xint | int) as x
     { INT (clean_number x, false)  }
 | (uint32l | uint32 | xint32 | int32) as x (* TODO: separate these out and check bounds *)
     { INT32 (Int32.of_string (clean_number x), false) }
 | (uint64 | int64) as x
     { INT64 (Int64.of_string (clean_number x), false) }
 | (ieee64 | xieee64) as x
     { IEEE64 (float_of_string x) }
 | (int | xint | float) ident_char+
     { failwith "This is not a valid numeric literal." }

 | "(*"
     { comment false lexbuf }

 | "//"  [^'\n''\r']*
     { token lexbuf }

 | '"'
     { string (Buffer.create 0) lexbuf }

 | truewhite+
     { token lexbuf }

 | offwhite+
     { token lexbuf }

 | newline
     { L.new_line lexbuf; token lexbuf }

 | '`' '`'
     (([^'`' '\n' '\r' '\t'] | '`' [^'`''\n' '\r' '\t'])+) as id
   '`' '`'
     { IDENT id }

 | "~"         { TILDE (L.lexeme lexbuf) }
 | "/\\"       { CONJUNCTION }
 | "\\/"       { DISJUNCTION }
 | "<:"        { SUBTYPE }
 | "<@"        { SUBKIND }
 | "(|"        { LENS_PAREN_LEFT }
 | "|)"        { LENS_PAREN_RIGHT }
 | '#'         { HASH }
 | "&"         { AMP }
 | "&&"        { AMP_AMP }
 | "||"        { BAR_BAR }
 | "()"        { LPAREN_RPAREN }
 | '('         { LPAREN }
 | ')'         { RPAREN }
 | '*'         { STAR }
 | ','         { COMMA }
 | "~>"        { SQUIGGLY_RARROW }
 | "->"        { RARROW }
 | "<==>"      { IFF }
 | "==>"       { IMPLIES }
 | "."         { DOT }
 | "{:pattern" { LBRACE_COLON_PATTERN }
 | ":"         { COLON }
 | "::"        { COLON_COLON }
 | ":="        { COLON_EQUALS }
 | ";;"        { SEMICOLON_SEMICOLON }
 | ";"         { SEMICOLON }
 | "="         { EQUALS }
 | "%["        { PERCENT_LBRACK }
 | "!{"        { BANG_LBRACE }
 | "["         { LBRACK }
 | "[|"        { LBRACK_BAR }
 | "<"         { if is_typ_app lexbuf then TYP_APP_LESS else CUSTOM_OP("<")  }
 | ">"         { if is_typ_app_gt () then TYP_APP_GREATER else custom_op_parser lexbuf }
 | "]"         { RBRACK }
 | "|]"        { BAR_RBRACK }
 | "{"         { LBRACE }
 | "|"         { BAR }
 | "}"         { RBRACE }
 | "!"         { BANG }
 | "$"         { DOLLAR }
 | "\\"        { BACKSLASH }
 | ('/' | '%') as op { DIV_MOD_OP    (String.of_char op) }
 | '+'         { PLUS_OP }
 | '-'         { MINUS_OP }
 | custom_op   {CUSTOM_OP (L.lexeme lexbuf) }

 | _ { failwith "unexpected char" }
 | eof { lc := 1; EOF }

and custom_op_parser = parse
 | custom_op_char * {CUSTOM_OP(">" ^  L.lexeme lexbuf)}

and string buffer = parse
 |  '\\' (newline as x) anywhite*
    {
      L.new_line lexbuf;
      string buffer lexbuf; }

 | newline as x
    { Buffer.add_string buffer x;
      L.new_line lexbuf;
      string buffer lexbuf; }

 | escape_char as c
    { Buffer.add_char buffer (char_of_ec c.[1]);
      string buffer lexbuf }

 |  '"'
    { STRING (ba_of_string (Buffer.contents buffer)) }

 |  '"''B'
    { BYTEARRAY (ba_of_string (Buffer.contents buffer)) }

 | _ as c
    { Buffer.add_char buffer c;
      string buffer lexbuf }

 | eof
    { failwith "unterminated string" }

and comment inner = parse

 | "(*"
    { let close_eof = comment true lexbuf in comment inner lexbuf }

 | newline
    { L.new_line lexbuf; comment inner lexbuf }

 | "*)"
    { if inner then EOF else token lexbuf }

 | _
    { comment inner lexbuf }

 | eof
     { lc := 1; EOF }

and cpp_filename = parse
 | ' ' '"' [^ '"']+ '"'
     { let s = trim_both lexbuf 2 1 in
       ignore_endline lexbuf }

and ignore_endline = parse
 | ' '* newline
     { token lexbuf }

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

  let split_on_char sep s =
     let open String in
     let r = ref [] in
     let j = ref (length s) in
     for i = length s - 1 downto 0 do
        if unsafe_get s i = sep then begin
          r := sub s (i + 1) (!j - i - 1) :: !r;
          j := i
        end
     done;
     sub s 0 !j :: !r

  let string_trim_both s n m = BatString.sub s n (String.length s - (n+m))
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
    Hashtbl.add keywords "abstract"      ABSTRACT    ;
    Hashtbl.add keywords "attributes"    ATTRIBUTES  ;
    Hashtbl.add keywords "noeq"          NOEQUALITY  ;
    Hashtbl.add keywords "unopteq"       UNOPTEQUALITY  ;
    Hashtbl.add keywords "and"           AND         ;
    Hashtbl.add keywords "assert"        ASSERT      ;
    Hashtbl.add keywords "assume"        ASSUME      ;
    Hashtbl.add keywords "begin"         BEGIN       ;
    Hashtbl.add keywords "by"            BY          ;
    Hashtbl.add keywords "default"       DEFAULT     ;
    Hashtbl.add keywords "effect"        EFFECT      ;
    Hashtbl.add keywords "else"          ELSE        ;
    Hashtbl.add keywords "end"           END         ;
    Hashtbl.add keywords "ensures"       ENSURES     ;
    Hashtbl.add keywords "exception"     EXCEPTION   ;
    Hashtbl.add keywords "exists"        EXISTS      ;
    Hashtbl.add keywords "false"         FALSE       ;
    Hashtbl.add keywords "False"         L_FALSE     ;
    Hashtbl.add keywords "forall"        FORALL      ;
    Hashtbl.add keywords "fun"           FUN         ;
    Hashtbl.add keywords "function"      FUNCTION    ;
    Hashtbl.add keywords "if"            IF          ;
    Hashtbl.add keywords "in"            IN          ;
    Hashtbl.add keywords "include"       INCLUDE     ;
    Hashtbl.add keywords "inline"        INLINE      ;
    Hashtbl.add keywords "inline_for_extraction"        INLINE_FOR_EXTRACTION      ;
    Hashtbl.add keywords "irreducible"   IRREDUCIBLE ;
    Hashtbl.add keywords "let"           (LET false) ;
    Hashtbl.add keywords "logic"         LOGIC       ;
    Hashtbl.add keywords "match"         MATCH       ;
    Hashtbl.add keywords "module"        MODULE      ;
    Hashtbl.add keywords "mutable"       MUTABLE     ;
    Hashtbl.add keywords "new"           NEW         ;
    Hashtbl.add keywords "new_effect"    NEW_EFFECT  ;
    Hashtbl.add keywords "noextract"     NOEXTRACT   ;
    Hashtbl.add keywords "of"            OF          ;
    Hashtbl.add keywords "open"          OPEN        ;
    Hashtbl.add keywords "opaque"        OPAQUE      ;
    Hashtbl.add keywords "private"       PRIVATE     ;
    Hashtbl.add keywords "rec"           REC         ;
    Hashtbl.add keywords "reifiable"     REIFIABLE   ;
    Hashtbl.add keywords "reify"         REIFY       ;
    Hashtbl.add keywords "reflectable"   REFLECTABLE ;
    Hashtbl.add keywords "requires"      REQUIRES    ;
    Hashtbl.add keywords "sub_effect"    SUB_EFFECT  ;
    Hashtbl.add keywords "then"          THEN        ;
    Hashtbl.add keywords "total"         TOTAL       ;
    Hashtbl.add keywords "true"          TRUE        ;
    Hashtbl.add keywords "True"          L_TRUE      ;
    Hashtbl.add keywords "try"           TRY         ;
    Hashtbl.add keywords "type"          TYPE        ;
    Hashtbl.add keywords "unfold"        UNFOLD      ;
    Hashtbl.add keywords "unfoldable"    UNFOLDABLE  ;
    Hashtbl.add keywords "val"           VAL         ;
    Hashtbl.add keywords "when"          WHEN        ;
    Hashtbl.add keywords "with"          WITH        ;
    Hashtbl.add keywords "_"             UNDERSCORE

  type delimiters = { angle:int ref; paren:int ref; }

  let ba_of_string s = Array.init (String.length s) (fun i -> Char.code (String.get s i))
  let n_typ_apps = ref 0
  let is_typ_app lexbuf =
    if not (FStar_Options.fs_typ_app lexbuf.lex_start_p.pos_fname) then false
    else try
      let char_ok = function
        | '(' | ')' | '<' | '>' | '*' | '-' | '\'' | '_' | ',' | '.' | ' ' | '\t' -> true
        | c when c >= 'A' && c <= 'Z' -> true
        | c when c >= 'a' && c <= 'z' -> true
        | c when c >= '0' && c <= '9' -> true
        | _ -> false
      in
      let balanced (contents:string) pos =
      if contents.[pos] <> '<'
      then (failwith  "Unexpected position in is_typ_lapp");
      let d = {angle=ref 1; paren=ref 0} in
      let upd i = match contents.[i] with
        | '(' -> incr d.paren
        | ')' -> decr d.paren
        | '<' -> incr d.angle
        | '>' when contents.[i-1] <> '-' -> decr d.angle
        | _ -> ()
      in
      let ok () = !(d.angle) >= 0 && !(d.paren) >= 0 in
      let rec aux i =
        if !(d.angle)=0 && !(d.paren)=0 then true
        else if i >= String.length contents || not (ok ()) || (not (char_ok (contents.[i]))) || FStar_Util.(starts_with (substring_from contents (Z.of_int i)) "then") then false
        else (upd i; aux (i + 1))
      in
      aux (pos + 1)
    in
    let rest = String.sub lexbuf.lex_buffer lexbuf.lex_last_pos (lexbuf.lex_buffer_len - lexbuf.lex_last_pos) in
    if not (String.contains rest '\n') then (lexbuf.refill_buff lexbuf);
    let lookahead =
      String.sub lexbuf.lex_buffer
                 (lexbuf.lex_last_pos - 1)
                 (lexbuf.lex_buffer_len - lexbuf.lex_last_pos + 1)
    in
    let res = balanced lookahead 0 in
    if res then incr n_typ_apps;
    (*Printf.printf "TYP_APP %s: %s\n" lookahead (if res then "YES" else "NO");*)
    res
  with e -> Printf.printf "Resolving typ_app<...> syntax failed.\n"; false

  let is_typ_app_gt () =
    if !n_typ_apps > 0
    then (decr n_typ_apps; true)
    else false

  let lc = ref 1
  let rec mknewline n lexbuf =
    if n > 0 then (L.new_line lexbuf; incr lc; mknewline (n-1) lexbuf)

  let clean_number x = String.strip ~chars:"uzyslLUnIN" x

  let comments : (string * FStar_Range.range) list ref = ref []

  let flush_comments () =
    let lexed_comments = !comments in
    comments := [] ;
    lexed_comments

  (* Try to trim each line of [comment] by the ammount of space
     on the first line of the comment if possible *)
  (* TODO : apply this to FSDOC too *)
  let maybe_trim_lines start_column comment =
    if start_column = 0 then comment
    else
      let comment_lines = split_on_char '\n' comment in
      let ensures_empty_prefix k s =
        let j = min k (String.length s - 1) in
        let rec aux i = if i > j then k else if s.[i] <> ' ' then i else aux (i+1) in
        aux 0
      in
      let trim_width =
        List.fold_left ensures_empty_prefix start_column comment_lines
      in
      String.concat "\n" (List.map (fun s -> String.tail s trim_width) comment_lines)


  let comment_buffer = Buffer.create 1024

  let start_comment lexbuf =
    Buffer.add_bytes comment_buffer "(*" ;
    (false, comment_buffer, fst (L.range lexbuf))

  let terminate_comment buffer startpos lexbuf =
    let endpos = snd (L.range lexbuf) in
    Buffer.add_bytes buffer "*)" ;
    let comment = Buffer.contents buffer in
    let comment = maybe_trim_lines (startpos.pos_cnum - startpos.pos_bol) comment in
    Buffer.clear buffer ;
    comments := (comment, FStar_Parser_Util.mksyn_range startpos endpos) :: ! comments

  let push_one_line_comment lexbuf =
    let startpos, endpos = L.range lexbuf in
    assert (startpos.pos_lnum = endpos.pos_lnum) ;
    comments := (lexeme lexbuf, FStar_Parser_Util.mksyn_range startpos endpos) :: !comments
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
let integer = digit+
let any_integer = xinteger | integer
let unsigned = 'u' | 'U'
let int8 = any_integer 'y'
let uint8 = any_integer unsigned 'y'
let int16 = any_integer 's'
let uint16 = any_integer unsigned 's'
let int32 = any_integer 'l'
let uint32 = any_integer unsigned 'l'
let int64 = any_integer 'L'
let uint64 = any_integer unsigned 'L'
let char8 = any_integer 'z'

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

let op_prefix  = ['!' '~' '?']
let op_infix0a = ['|'] (* left *)
let op_infix0b = ['&'] (* left *)
let op_infix0c = ['=' '<' '>'] (* left *)
let op_infix0c_nogt = ['=' '<'] (* left *)
let op_infix0d = ['$'] (* left *)

let op_infix0  = op_infix0a | op_infix0b | op_infix0c | op_infix0d
let op_infix1  = ['@' '^'] (* right *)
let op_infix2  = ['+' '-'] (* left *)
let op_infix3  = ['*' '/' '%'] (* left *)
let symbolchar = op_prefix | op_infix0 | op_infix1 | op_infix2 | op_infix3 | ['.' ':']


(* -------------------------------------------------------------------- *)
let escape_char = ('\\' ( '\\' | "\"" | '\'' | 'n' | 't' | 'b' | 'r'))
let char        = [^'\\''\n''\r''\t''\b'] | escape_char

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
     { FStar_Options.add_light_off_file lexbuf.lex_start_p.pos_fname ; PRAGMALIGHT }
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
 | '`'
    { BACKTICK }
 | ident as id
     { id |> Hashtbl.find_option keywords |> Option.default (IDENT id) }
 | constructor as id
     { NAME id }
 | tvar as id
     { TVAR id }
 | (integer | xinteger) as x
     { INT (clean_number x, false)  }
 (* TODO: check bounds!! *)
 | uint8 as x
     { UINT8 (clean_number x) }
 | char8 as x
     { CHAR (Char.chr (
       let x = int_of_string (clean_number x) in
       if x < 0 || x > 255 then
         failwith "Out-of-range character literal";
       x
       )) }
 | int8 as x
     { INT8 (clean_number x, false) }
 | uint16 as x
     { UINT16 (clean_number x) }
 | int16 as x
     { INT16 (clean_number x, false) }
 | uint32 as x
     { UINT32 (clean_number x) }
 | int32 as x
     { INT32 (clean_number x, false) }
 | uint64 as x
     { UINT64 (clean_number x) }
 | int64 as x
     { INT64 (clean_number x, false) }
 | (ieee64 | xieee64) as x
     { IEEE64 (float_of_string x) }
 | (integer | xinteger | float) ident_char+
     { failwith "This is not a valid numeric literal." }

 | "(*" '*'* "*)"
     { token lexbuf }

 | "(**"
     { fsdoc (1,"",[]) lexbuf}

 | "(*"
     { let inner, buffer, startpos = start_comment lexbuf in
       comment inner buffer startpos lexbuf }

 | "//"  [^'\n''\r']*
     { push_one_line_comment lexbuf ;
       token lexbuf }

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
 | "-"         { MINUS }
 | "/\\"       { CONJUNCTION }
 | "\\/"       { DISJUNCTION }
 | "<:"        { SUBTYPE }
 | "<@"        { SUBKIND }
 | "(|"        { LENS_PAREN_LEFT }
 | "|)"        { LENS_PAREN_RIGHT }
 | '#'         { HASH }
 | "u#"        { UNIV_HASH }
 | "&"         { AMP }
 | "()"        { LPAREN_RPAREN }
 | '('         { LPAREN }
 | ')'         { RPAREN }
 | ','         { COMMA }
 | "~>"        { SQUIGGLY_RARROW }
 | "->"        { RARROW }
 | "<--"       { LONG_LEFT_ARROW }
 | "<-"        { LARROW }
 | "<==>"      { IFF }
 | "==>"       { IMPLIES }
 | "."         { DOT }
 | "?."        { QMARK_DOT }
 | "?"         { QMARK }
 | ".["        { DOT_LBRACK }
 | ".("        { DOT_LPAREN }
 | "{:pattern" { LBRACE_COLON_PATTERN }
 | ":"         { COLON }
 | "::"        { COLON_COLON }
 | ":="        { COLON_EQUALS }
 | ";;"        { SEMICOLON_SEMICOLON }
 | ";"         { SEMICOLON }
 | "="         { EQUALS }
 | "%["        { PERCENT_LBRACK }
 | "!{"        { BANG_LBRACE }
 | "[@"        { LBRACK_AT }
 | "["         { LBRACK }
 | "[|"        { LBRACK_BAR }
 | "<"         { if is_typ_app lexbuf then TYP_APP_LESS else OPINFIX0c("<")  }
 | ">"         { if is_typ_app_gt () then TYP_APP_GREATER else symbolchar_parser lexbuf }
 | "|>"        { PIPE_RIGHT }
 | "]"         { RBRACK }
 | "|]"        { BAR_RBRACK }
 | "{"         { LBRACE }
 | "|"         { BAR }
 | "}"         { RBRACE }
 | "$"         { DOLLAR }

 (* Operators. *)
 | op_prefix  symbolchar* { OPPREFIX (L.lexeme lexbuf) }
 | op_infix0a symbolchar* { OPINFIX0a (L.lexeme lexbuf) }
 | op_infix0b symbolchar* { OPINFIX0b (L.lexeme lexbuf) }
 | op_infix0c_nogt symbolchar* { OPINFIX0c (L.lexeme lexbuf) }
 | op_infix0d symbolchar* { OPINFIX0d (L.lexeme lexbuf) }
 | op_infix1  symbolchar* { OPINFIX1 (L.lexeme lexbuf) }
 | op_infix2  symbolchar* { OPINFIX2 (L.lexeme lexbuf) }
 | "**"       symbolchar* { OPINFIX4 (L.lexeme lexbuf) }
 | op_infix3  symbolchar* { OPINFIX3 (L.lexeme lexbuf) }


 | _ { failwith "unexpected char" }
 | eof { lc := 1; EOF }

and symbolchar_parser = parse
 | symbolchar* { OPINFIX0c (">" ^  L.lexeme lexbuf) }

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

and comment inner buffer startpos = parse

 | "(*"
    { Buffer.add_bytes buffer "(*" ;
      let close_eof = comment true buffer startpos lexbuf in
      comment inner buffer startpos lexbuf }

 | newline
    { Buffer.add_char buffer '\n' ;
      L.new_line lexbuf;
      comment inner buffer startpos lexbuf }

 | "*)"
    { terminate_comment buffer startpos lexbuf;
      if inner then EOF else token lexbuf }

 | _ as c
    { Buffer.add_char buffer c ;
      comment inner buffer startpos lexbuf }

 | eof
     { terminate_comment buffer startpos lexbuf;
       lc := 1; EOF }

and fsdoc cargs = parse
 | '(' '*'
    { let n,doc,kw = cargs in
      fsdoc (n+1,doc^"(*",kw) lexbuf }

 | "*)" newline newline
    { let n,doc,kw = cargs in
	  mknewline 2 lexbuf;
      if n > 1 then fsdoc (n-1,doc^(L.lexeme lexbuf),kw) lexbuf
      else FSDOC_STANDALONE(doc,kw) }

 | "*)" newline
    { let n,doc,kw = cargs in
	  mknewline 1 lexbuf;
      if n > 1 then fsdoc (n-1,doc^(L.lexeme lexbuf),kw) lexbuf
      else FSDOC(doc,kw) }

 | newline "\\@"
    { let n,doc,kw = cargs in
	  mknewline 1 lexbuf;
	  let nl = trim_right lexbuf 2 in
	  fsdoc(n,doc^nl^"@",kw) lexbuf}

 | newline "@"
	 { let n,doc,kw = cargs in
	   mknewline 1 lexbuf;
	   fsdoc_kw (n,doc,kw) lexbuf}

 | newline
    { let n,doc,kw = cargs in
      mknewline 1 lexbuf;
      fsdoc (n,doc^(L.lexeme lexbuf),kw) lexbuf }

 | _ { let n,doc,kw = cargs in
       fsdoc(n,doc^(L.lexeme lexbuf),kw) lexbuf }

and fsdoc_kw cargs = parse
 | anywhite*
     {fsdoc_kw cargs lexbuf}
 | ['a'-'z' 'A'-'Z']+
     { let n,doc,kw = cargs in
	   fsdoc_kw_arg(n,doc,kw,L.lexeme lexbuf,"") lexbuf }
 | _ { failwith "Invalid FSDoc keyword, use \\@ if a line starts with an @ sign" }

and fsdoc_kw_arg cargs = parse
 | newline
     { let n,doc,kw,kwn,kwa = cargs in
	   fsdoc(n,doc^(L.lexeme lexbuf),(kwn,kwa)::kw) lexbuf}
 | _ { let n,doc,kw,kwn,kwa = cargs in
       fsdoc_kw_arg(n,doc,kw,kwn,kwa^(L.lexeme lexbuf)) lexbuf }

and cpp_filename = parse
 | ' ' '"' [^ '"']+ '"'
     { let s = trim_both lexbuf 2 1 in
       ignore_endline lexbuf }

and ignore_endline = parse
 | ' '* newline
     { token lexbuf }

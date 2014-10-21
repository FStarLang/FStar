{
  open FSLangParser

  module L : sig
    include module type of struct include Lexing end

    val range : lexbuf -> position * position
  end = struct
    include Lexing

    let range (lexbuf : lexbuf) =
      (lexeme_start_p lexbuf, lexeme_end_p lexbuf)
  end

  let is_typ_app = fun _ -> true
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
let trigraph           = '\\' digit digit digit
let hexgraph_short     = '\\' 'x' hex hex 
let unicodegraph_short = '\\' 'u' hex hex hex hex
let unicodegraph_long  = '\\' 'U' hex hex hex hex hex hex hex hex

(* -------------------------------------------------------------------- *)
let escape_char = ('\\' ( '\\' | "\"" | '\'' | 'n' | 't' | 'b' | 'r'))
let char        = '\'' ( [^'\\''\n''\r''\t''\b'] | escape_char) '\''

(* -------------------------------------------------------------------- *)
let constructor_start_char = upper
let ident_start_char       = lower  | '_'
let ident_char             = letter | digit  | ['\'']
let tvar_char              = letter | digit 

let constructor = constructor_start_char ident_char*  
let ident       = ident_start_char ident_char*
let tvar        = '\'' (ident_start_char | constructor_start_char) tvar_char*
let basekind    = '*' | 'A' | 'E' | "Prop"

rule token = parse
 | "#monadic"
     { PRAGMAMONADIC }
 | "#light"
     { PRAGMALIGHT }
 | ident
     { IDENT (L.lexeme lexbuf) }   (* FIXME: keywords *)
 | constructor
     { NAME (L.lexeme lexbuf) }
 | tvar 
     { TVAR (L.lexeme lexbuf) }
 | xint | int | xint32 | int32 
     { INT32 (Int32.zero, false) }
 | int64 
     { INT64 (Int64.zero, false) }
 | ieee64 | xieee64     
     { IEEE64 0. }
 | (int | xint | float) ident_char+
     { failwith "This is not a valid numeric literal." }
 | char
     { CHAR '\000' }
 | char 'B' 
     { CHAR '\000' }
 | '\'' trigraph '\''
     { CHAR '\000' }

 | '\'' hexgraph_short     '\'' { CHAR '\000' }
 | '\'' unicodegraph_short '\'' { CHAR '\000' }
 | '\'' unicodegraph_long  '\'' { CHAR '\000' }

 | "~"         { TILDE (L.lexeme lexbuf) }
 | "/\\"       { CONJUNCTION }
 | "\\/"       { DISJUNCTION }
 | "<:"        { SUBTYPE }
 | "<@"        { SUBKIND }
 | "(|"        { LENS_PAREN_LEFT }
 | "|)"        { LENS_PAREN_RIGHT }
 | '#'         { HASH }
 | "&&"        { AMP_AMP }
 | "||"        { BAR_BAR }
 | "()"        { LPAREN_RPAREN }
 | '('         { LPAREN }
 | ')'         { RPAREN }
 | '*'         { STAR }
 | ','         { COMMA }
 | "~>"        { SQUIGGLY_RARROW }
 | "->"        { RARROW }
 | "=>"        { RRARROW }
 | "<==>"      { IFF }
 | "==>"       { IMPLIES }
 | "."         { DOT }
 | "{:pattern" { LBRACE_COLON_PATTERN }
 | ":"         { COLON }
 | "::"        { COLON_COLON }
 | "@"         { ATSIGN }
 | "^"         { HAT }
 | ":="        { COLON_EQUALS }
 | ";;"        { SEMICOLON_SEMICOLON }
 | ";"         { SEMICOLON }
 | "=!="       { EQUALS_BANG_EQUALS }
 | "=="        { EQUALS_EQUALS }
 | "="         { EQUALS }
 | "["         { LBRACK }
 | "[|"        { LBRACK_BAR }
 | "<="        { LEQ }
 | ">="        { GEQ }
 | "<>"        { LESSGREATER }
 | "<"         { if is_typ_app lexbuf then TYP_APP_LESS else LESS  }
 | ">"         { GREATER }
 | "|>"        { PIPE_RIGHT }
 | "<|"        { PIPE_LEFT }
 | "]"         { RBRACK }
 | "|]"        { BAR_RBRACK }
 | "{"         { LBRACE }
 | "|"         { BAR }
 | "}"         { RBRACE }
 | "!"         { BANG (L.lexeme lexbuf) }

 | ('/' | '%') { DIV_MOD_OP (L.lexeme lexbuf) }
 | ('+' | '-') { PLUS_MINUS_OP (L.lexeme lexbuf) }

 | "(*"
     { comment lexbuf; token lexbuf }

 | "//"  [^'\n''\r']* 
     { token lexbuf }

 | '"' 
     { string lexbuf; STRING "" }

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

 | _ { failwith "unexpected char" }     

 | eof { EOF }

and string = parse
 |  '\\' newline anywhite* 
    { L.new_line lexbuf; string lexbuf; }

 | newline
    { L.new_line lexbuf; string lexbuf; }

 | escape_char
    { string lexbuf } 

 | trigraph
    { string lexbuf }

 | hexgraph_short
    { string lexbuf  }
      
 | unicodegraph_short
    { string lexbuf  }
     
 | unicodegraph_long
    { string lexbuf  }
     
 |  '"' 
    { () }

 |  '"''B' 
    { () }

 | ident  
    { string lexbuf }

 | xinteger
    { string lexbuf }

 | anywhite+  
    { string lexbuf }

 | _ 
    { string lexbuf }

 | eof  
    { failwith "unterminated string" }

and comment = parse
 | char
    { comment lexbuf }
    
 | '"'   
    { comment_string lexbuf; comment lexbuf; }

 | "(*"
    { comment lexbuf; comment lexbuf; }
     
 | newline
    { L.new_line lexbuf; comment lexbuf; }

 | "*)" 
    { () }
      
 | [^ '\'' '(' '*' '\n' '\r' '"' ')' ]+
    { comment lexbuf }
    
 | _
    { comment lexbuf }

 | eof 
     { failwith "unterminated comment" }

and comment_string = parse
 | '\\' newline anywhite* 
     { L.new_line lexbuf; comment_string lexbuf }

 | newline 
     { L.new_line lexbuf; comment_string lexbuf }

 | '"' 
     { () }

 | escape_char
 | trigraph
 | hexgraph_short
 | unicodegraph_short
 | unicodegraph_long
 | ident  
 | xinteger
 | anywhite+
     { comment_string lexbuf }

 | _  
     { comment_string lexbuf }

 | eof 
     { failwith "unterminated comment" }

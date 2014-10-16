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

(* -------------------------------------------------------------------- *)
rule main = parse
| _ { assert false }

{
  open InteractiveParser
  open Lexing
}

let newline    = ('\n' | '\r' '\n')
let notnewline = [^'\n''\r']
let integer    = ['0' - '9']+

rule token = parse
  | newline     { EOL }
  | "#push"     { PUSH }
  | "#pop"      { POP }
  | "#done"     { DONE }
  | integer     { INT (int_of_string (lexeme lexbuf)) }
  | notnewline* { LINE (lexeme lexbuf) }

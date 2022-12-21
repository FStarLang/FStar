{
open Pulseparser
}

let space = " " | "\t"
let newline = "\r" | "\r\n" | "\n"
let digit = ['0'-'9']

let low_alpha = ['a'-'z']
let up_alpha =  ['A'-'Z']
let any = up_alpha | low_alpha | "_" | digit

let ident_start = low_alpha | up_alpha | "_"
let ident = ident_start any*

rule token =
  parse
  | ident as i
    {
      if i = "true" then TRUE
      else if i = "false" then FALSE
      else if i = "emp" then EMP
      else if i = "fun" then FUN
      else IDENT (i)
    }
  | "("           { LPAREN }
  | ")"           { RPAREN }
  | "{"           { LBRACE }
  | "}"           { RBRACE }
  | ","           { COMMA }
  | "."           { DOT }
  | "->"          { RARROW }
  | "*"           { STAR }
  | ":"           { COLON }
  | space+        { token lexbuf }
  | newline       { Lexing.new_line lexbuf; token lexbuf }
  | eof           { EOF }

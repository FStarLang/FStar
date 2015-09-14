{
open Lexing
open Wparser

exception Eof

let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
  lexbuf.Lexing.lex_curr_p <-
  { pos with
    Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
    Lexing.pos_bol = pos.Lexing.pos_cnum;
  }
}

let var_head = ['a'-'z' '_']
let var_num = ['a'-'z' 'A'-'Z' '0'-'9' '_' '\'']
let var = var_head var_num*

let num = ['0'-'9']+

let bang = ['!']

let eol = '\n' | '\r' | "\r\n"

rule token = parse
  | [' ' '\t']      { token lexbuf                       }
  | eol             { incr_linenum lexbuf ; token lexbuf }
  | '.'             { DOT                                }
  | '|'             { BAR                                }
  | ';'             { SEMICOLON                          }
  | '('	            { LPAREN                             }
  | ')'	            { RPAREN                             }
  | '['	            { LBRACKET                           }
  | ']'	            { RBRACKET                           }
  | '='	            { EQUAL                              }
  | "->"            { RARROW                             }
  | "in"            { IN                                 }
  | "let"           { LET                                }
  | "true"          { TRUE                               }
  | "false"         { FALSE                              }
  | "()"            { UNIT                               }
  | "as_par"        { ASPAR                              }
  | "as_sec"        { ASSEC                              }
  | "unbox_p"       { UNBOX                              }
  | "unbox_s"       { UNBOX                              }
  | "mkwire_p"      { MKWIRE                             }
  | "mkwire_s"      { MKWIRE                             }
  | "projwire_p"    { PROJWIRE                           }
  | "projwire_s"    { PROJWIRE                           }
  | "concat_wire"   { CONCATWIRE                         }
  | "fun"           { FUN                                }
  | "fix"           { FIX                                }
  | "apply"         { APPLY                              }
  | "match"         { MATCH                              }
  | "with"          { WITH                               }
  | "end"           { END                                }
  | "ffi"           { FFI                                }

  | var as v        { VAR v   }
  | num as n        { NUM (int_of_string n) }

  | eof     { EOF }

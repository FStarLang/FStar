open Lexing
open FStar_Pervasives_Native
open FStar_Pervasives
open FStar_Compiler_Range

let pos_as_range lexbuf =
  FStar_Parser_Util.getLexerRange lexbuf

let parse (s:string) (r:range) =
  let p = Pulseparser.prog in
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- {
    pos_fname= file_of_range r;
    pos_cnum = Z.to_int (col_of_pos (start_of_range r));
    pos_bol = 0;
    pos_lnum = Z.to_int (line_of_pos (start_of_range r)) };
  try
    match p Pulselexer.token lexbuf with
    | Some e -> Inl e
    | None -> Inr ("Parser parsed None", pos_as_range lexbuf)
  with
  | Pulse_Util.Syntax_error msg ->
    Inr ("Syntax error: " ^msg, pos_as_range lexbuf)
  | _ ->
    Inr ("Syntax error", pos_as_range lexbuf)

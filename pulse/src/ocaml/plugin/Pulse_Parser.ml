open Lexing
open FStar_Pervasives_Native
open FStar_Pervasives
open FStar_Compiler_Range
open FStar_Parser_ParseIt

let pos_as_range lexbuf =
  FStar_Parser_Util.getLexerRange lexbuf

(*
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
    *)

let parse (s:string) (r:range) =
  print_string ("About to parse <" ^ s ^ ">");
  let frag = {
    frag_fname=file_of_range r;
    frag_text=s;
    frag_line=(line_of_pos (start_of_range r));
    frag_col=(col_of_pos (start_of_range r));
  } in
  match FStar_Parser_ParseIt.parse (Toplevel frag) with
  | ASTFragment(Inr decls, comments) ->
    FStar_Compiler_Util.print1 ("Successfully parsed %s\n, got errors")
      (String.concat "\n" (List.map FStar_Parser_AST.decl_to_string decls));
    Inl (List.hd decls)
  | ParseError(_, s, r) -> 
    Inr (s, r)

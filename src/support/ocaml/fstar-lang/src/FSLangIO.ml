(* -------------------------------------------------------------------- *)
module B = BatPervasives
module P = FSLangParser
module L = Lexing

(* -------------------------------------------------------------------- *)
type program = unit

(* -------------------------------------------------------------------- *)
let lexbuf_from_channel = fun name channel ->
  let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = name;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

(* -------------------------------------------------------------------- *)
let parserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised FSLangParser.file

type parser_t =
  (P.token * L.position * L.position, unit list)
    MenhirLib.Convert.revised

(* -------------------------------------------------------------------- *)
let lexer lexbuf = fun () ->
  let token = FSLangLexer.token lexbuf in
  (token, L.lexeme_start_p lexbuf, L.lexeme_end_p lexbuf)

(* -------------------------------------------------------------------- *)
let from_channel ~name channel =
  let lexbuf = lexbuf_from_channel name channel in
  parserfun () (lexer lexbuf)

(* -------------------------------------------------------------------- *)
let from_file filename =
  let channel = open_in filename in

  B.finally
    (fun () -> close_in channel)
    (from_channel ~name:filename) channel

(* -------------------------------------------------------------------- *)
let from_string data =
  parserfun() (lexer (Lexing.from_string data))

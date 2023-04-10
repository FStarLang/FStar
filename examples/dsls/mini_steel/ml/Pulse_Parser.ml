open Lexing

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.fprintf outx "%s:%d:%d"
    pos.pos_fname
    pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse (s:string) =
  let p = Pulseparser.prog in
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- {
    pos_fname= "";
    pos_cnum = 0;
    pos_bol = 0;
    pos_lnum = 1 };
  try
    match p Pulselexer.token lexbuf with
    | Some e -> e
    | None -> print_string "Parser parsed None"; exit 1
  with e ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit 1

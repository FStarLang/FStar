open X86Interpreter

let () =
  let _ =
    if (Array.length Sys.argv < 2) || (Array.length Sys.argv > 2) then
      (Format.printf "Usage: autopar <file>\n";
       exit 0) in
  let filearg = 1 in
  let file = open_in (Sys.argv.(filearg)) in
  let lexbuf = Lexing.from_channel file in
  let progstmt =
    try Parser.program Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at line %d\n" pos.Lexing.pos_lnum;
      exit 1 in
	
  let _ = interpret progstmt (fun _ ->(FStar_UInt64.uint_to_t  (Prims.parse_int "0"))) (fun _ ->(FStar_UInt64.uint_to_t  (Prims.parse_int "0"))) in
  ()

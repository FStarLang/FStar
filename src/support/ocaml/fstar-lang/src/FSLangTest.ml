(* -------------------------------------------------------------------- *)
open FSLangIO

(* -------------------------------------------------------------------- *)
let () =
  if (Array.length Sys.argv)-1 <> 1 then
    failwith "Usage: parser [file.fst]";
  try
    let (_ : program) = FSLangIO.from_file Sys.argv.(1) in ()
  with FSLangAst.ParseError lc ->
    Printf.printf "parse error at %d:%d\n%!"
      lc.Lexing.pos_lnum lc.Lexing.pos_bol;
    exit 1

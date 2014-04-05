module Microsoft.FStar.Parser.ParseIt
open Microsoft.FStar
open Microsoft.FStar.Util

let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) = 
  lexbuf.EndPos <- {lexbuf.EndPos with 
    pos_fname= Range.encode_file filename; 
    pos_cnum=0;
    pos_lnum=1 }

let parse_file fn = 
  Parse.warningHandler := (function
    | Lexhelp.ReservedKeyword(m,s) -> Printf.printf "%s:%s" (Range.string_of_range s) m
    | e -> Printf.printf "Warning: %A\n" e);
  
  let filename,sr = match fn with 
    | Inl (filename:string) -> filename, 
      (try new System.IO.StreamReader(filename) :> System.IO.TextReader
       with _ -> raise (Absyn.Syntax.Err (Util.format1 "Unable to open file: %s" filename)))
    | Inr (s:string) -> "<input>", new System.IO.StringReader(s) :> System.IO.TextReader in

  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename) in 
  let lexer = LexFStar.token lexargs in 
  try
    Inl (Parse.file lexer lexbuf)
  with 
    | Absyn.Syntax.Error(msg, r) -> 
      let msg = Util.format2 "ERROR %s: %s\n" (Range.string_of_range r) msg in
      Inr msg
    | e ->
      let pos = lexbuf.EndPos in
      Inr  (Util.format3 "ERROR: Syntax error near line %s, character %s in file %s\n" 
              (Util.string_of_int pos.pos_lnum) 
              (Util.string_of_int (pos.pos_cnum - pos.pos_bol))
              filename)

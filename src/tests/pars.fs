#light "off"
module FStar.Tests.Pars
open FStar
open FStar.Range
open FStar.Parser
let pars s = 
  let resetLexbufPos filename (lexbuf: Microsoft.FSharp.Text.Lexing.LexBuffer<char>) =
    lexbuf.EndPos <- {lexbuf.EndPos with
    pos_fname= Range.encode_file filename;
    pos_cnum=0;
    pos_lnum=1 } in
  let filename,sr,fs = "<input>", new System.IO.StringReader(s) :> System.IO.TextReader, s  in
  let lexbuf = Microsoft.FSharp.Text.Lexing.LexBuffer<char>.FromTextReader(sr) in
  resetLexbufPos filename lexbuf;
  let lexargs = Lexhelp.mkLexargs ((fun () -> "."), filename,fs) in
  let lexer = LexFStar.token lexargs in
  let t = Parser.Parse.term lexer lexbuf in
  let env = Parser.Env.empty_env () in
  Parser.ToSyntax.desugar_term env t



#light "off"
module FStar.Tests.Pars
open FStar
open FStar.Range
open FStar.Parser
open FStar.Util

let env = ref None

let init () =
    Options.universes := true;
    let prims = Options.prims() in
    match ParseIt.parse (Inl prims) with 
        | Inl (Inl [m]) -> 
          let env', _ = Parser.ToSyntax.desugar_modul (Parser.Env.empty_env()) m in
          let env' , _ = FStar.Parser.Env.prepare_module_or_interface false false env' (FStar.Ident.lid_of_path ["Test"] (FStar.Range.dummyRange)) in
          env := Some env';
          env'
        | _ -> failwith "Unexpected "


let pars s = 
  try 
      let env = match !env with 
        | None -> init()
        | Some env -> env in
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
      Parser.ToSyntax.desugar_term env t
 with 
    | FStar.Syntax.Syntax.Err msg ->
        printfn "Failed to parse %s\n%s\n" s msg;
        exit -1
    | FStar.Syntax.Syntax.Error(msg, r) ->
        printfn "Failed to parse %s\n%s: %s\n" s (Range.string_of_range r) msg;
        exit -1



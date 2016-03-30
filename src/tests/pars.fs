#light "off"
module FStar.Tests.Pars
open FStar
open FStar.Range
open FStar.Parser
open FStar.Util
open FStar.Syntax
module DsEnv = FStar.Parser.Env
module TcEnv = FStar.TypeChecker.Env
module SMT = FStar.SMTEncoding.Encode
module Tc = FStar.TypeChecker.Tc

let env = ref None
let tcenv = ref None

let parse_prims () =
    Options.universes := true;
    let prims = Options.prims() in
    match ParseIt.parse (Inl prims) with 
    | Inl (Inl [m]) -> 
        let env',  prims_mod = Parser.ToSyntax.desugar_modul (Parser.Env.empty_env()) m in
        let env' , _ = FStar.Parser.Env.prepare_module_or_interface false false env' (FStar.Ident.lid_of_path ["Test"] (FStar.Range.dummyRange)) in
        env := Some env';
        env', prims_mod
    | _ -> failwith "Unexpected "

let init_once () : unit =
  let solver = SMT.dummy in
  let env = TcEnv.initial_env Tc.type_of solver Const.prims_lid in
  env.solver.init env;
  let dsenv, prims_mod = parse_prims () in
  let prims_mod, env = Tc.check_module env prims_mod in
  tcenv := Some env

let rec init () = 
    match !env, !tcenv with 
        | Some e, Some f -> e, f
        | _ -> init_once(); init()

let pars s = 
  try 
      let env, _ = init() in
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



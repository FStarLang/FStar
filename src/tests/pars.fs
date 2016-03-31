#light "off"
module FStar.Tests.Pars
open FStar
open FStar.Range
open FStar.Parser
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
module DsEnv = FStar.Parser.Env
module TcEnv = FStar.TypeChecker.Env
module SMT = FStar.SMTEncoding.Encode
module Tc = FStar.TypeChecker.Tc

let test_lid = Ident.lid_of_path ["Test"] Range.dummyRange
let dsenv_ref = ref None
let tcenv_ref = ref None
let test_mod_ref = ref (Some ({name=test_lid;
                                declarations=[]; 
                                exports=[]; 
                                is_interface=false}))

let parse_prims () =
    Options.universes := true;
    let prims = Options.prims() in
    match ParseIt.parse (Inl prims) with 
    | Inl (Inl [m]) -> 
        let env',  prims_mod = Parser.ToSyntax.desugar_modul (Parser.Env.empty_env()) m in
        let env' , _ = FStar.Parser.Env.prepare_module_or_interface false false env' (FStar.Ident.lid_of_path ["Test"] (FStar.Range.dummyRange)) in
        dsenv_ref := Some env';
        env', prims_mod
    | _ -> failwith "Unexpected "

let init_once () : unit =
  let solver = SMT.dummy in
  let env = TcEnv.initial_env Tc.type_of solver Const.prims_lid in
  env.solver.init env;
  let dsenv, prims_mod = parse_prims () in
  let prims_mod, env = Tc.check_module env prims_mod in
  let env = TcEnv.set_current_module env test_lid in
  tcenv_ref := Some env

let rec init () = 
    match !dsenv_ref, !tcenv_ref with 
        | Some e, Some f -> e, f
        | _ -> init_once(); init()

let pars_term_or_fragment is_term s = 
  try 
      let env, tcenv = init() in
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
      if is_term 
      then let t = Parser.Parse.term lexer lexbuf in
           Some (Parser.ToSyntax.desugar_term env t)
      else begin match FStar.Universal.interactive_tc.check_frag (env, tcenv) !test_mod_ref s with 
                | Some (test_mod', (env', tcenv'), 0) ->
                  test_mod_ref := test_mod';
                  dsenv_ref := Some env';
                  tcenv_ref := Some tcenv';
                  None
                | _ -> raise (FStar.Syntax.Syntax.Err ("Failed to check fragment: " ^s))
            end
 with 
    | FStar.Syntax.Syntax.Err msg ->
        printfn "Failed to parse %s\n%s\n" s msg;
        exit -1
    | FStar.Syntax.Syntax.Error(msg, r) ->
        printfn "Failed to parse %s\n%s: %s\n" s (Range.string_of_range r) msg;
        exit -1

let failed_to_parse s e = 
    match e with 
        | FStar.Syntax.Syntax.Err msg ->
            printfn "Failed to parse %s\n%s\n" s msg;
            exit -1
        | FStar.Syntax.Syntax.Error(msg, r) ->
            printfn "Failed to parse %s\n%s: %s\n" s (Range.string_of_range r) msg;
            exit -1
        | _ -> raise e

let pars s = 
    try 
          let env, tcenv = init() in
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
        | e when not (!Options.trace_error) -> failed_to_parse s e

let tc s = 
    let tm = pars s in
    let _, tcenv = init() in
    let tm, _, _ = Tc.type_of tcenv tm in 
    tm

let pars_and_tc_fragment s = 
    Options.trace_error := true;
    let report () = FStar.TypeChecker.Errors.report_all () |> ignore in
    try
        let env, tcenv = init() in
        match FStar.Universal.interactive_tc.check_frag (env, tcenv) !test_mod_ref s with 
        | Some (test_mod', (env', tcenv'), n) ->
            test_mod_ref := test_mod';
            dsenv_ref := Some env';
            tcenv_ref := Some tcenv';
            if n <> 0
            then (report ();
                  raise (FStar.Syntax.Syntax.Err (Util.format1 "%s errors were reported" (string_of_int n))))
        | _ -> report(); raise (FStar.Syntax.Syntax.Err ("check_frag returned None: " ^s))
    with 
        | e when not (!Options.trace_error) -> failed_to_parse s e
            
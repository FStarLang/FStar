#light "off"
module FStar.Tests.Pars
//open FSharp.Compatibility.OCaml
open FStar
open FStar.All
open FStar.Range
open FStar.Parser
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Errors
open FStar.TypeChecker.Env
open FStar.Parser.ParseIt
module DsEnv = FStar.Syntax.DsEnv
module TcEnv = FStar.TypeChecker.Env
module SMT = FStar.SMTEncoding.Solver
module Tc = FStar.TypeChecker.Tc
module TcTerm = FStar.TypeChecker.TcTerm
module ToSyntax = FStar.ToSyntax.ToSyntax
module BU = FStar.Util
module D = FStar.Parser.Driver
module Rel = FStar.TypeChecker.Rel
module NBE = FStar.TypeChecker.NBE

let test_lid = Ident.lid_of_path ["Test"] Range.dummyRange
let tcenv_ref: ref<option<TcEnv.env>> = mk_ref None
let test_mod_ref = mk_ref (Some ({name=test_lid;
                                  declarations=[];
                                  exports=[];
                                  is_interface=false}))

let parse_mod mod_name dsenv =
    match parse (Filename mod_name) with
    | ASTFragment (Inl m, _) ->
        let m, env'= ToSyntax.ast_modul_to_modul m dsenv in
        let env' , _ = DsEnv.prepare_module_or_interface false false env' (FStar.Ident.lid_of_path ["Test"] (FStar.Range.dummyRange)) DsEnv.default_mii in
        env', m
    | ParseError (err, msg, r) ->
        raise (Error(err, msg, r))
    | ASTFragment (Inr _, _) ->
        let msg = BU.format1 "%s: expected a module\n" mod_name in
        raise_error (Errors.Fatal_ModuleExpected, msg) dummyRange
    | Term _ ->
        failwith "Impossible: parsing a Filename always results in an ASTFragment"

let add_mods mod_names dsenv env =
  List.fold_left (fun (dsenv,env) mod_name ->
      let dsenv, string_mod = parse_mod mod_name dsenv in
      let _mod, _, env = Tc.check_module env string_mod false in
      (dsenv, env)
  ) (dsenv,env) mod_names

let init_once () : unit =
  let solver = SMT.dummy in
  let env = TcEnv.initial_env
                FStar.Parser.Dep.empty_deps
                TcTerm.tc_term
                TcTerm.type_of_tot_term
                TcTerm.universe_of
                TcTerm.check_type_of_well_typed_term
                solver
                Const.prims_lid 
                NBE.normalize' in
  env.solver.init env;
  let dsenv, prims_mod = parse_mod (Options.prims()) (DsEnv.empty_env()) in
  let env = {env with dsenv=dsenv} in
  let _prims_mod, _, env = Tc.check_module env prims_mod false in
  // needed to run tests with chars
  // let dsenv, env = add_mods ["FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStar.Mul.fst"; "FStar.Squash.fsti";
  //                            "FStar.Classical.fst"; "FStar.List.Tot.Base.fst"; "FStar.List.Tot.Properties.fst"; "FStar.List.Tot.fst";
  //                            "FStar.StrongExcludedMiddle.fst"; "FStar.Seq.Base.fst"; "FStar.Seq.Properties.fst"; "FStar.Seq.fst";
  //                            "FStar.BitVector.fst"; "FStar.Math.Lib.fst"; "FStar.Math.Lemmas.fst"; "FStar.UInt.fst"; "FStar.UInt32.fst";
  //                            "FStar.Char.fsti"; "FStar.String.fsti"] dsenv env in

  // only needed to test tatic normalization
  // let dsenv, env = add_mods ["FStar.Range.fsti"; "FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStar.Reflection.Types.fsti"; "FStar.Order.fst";
  //                            "FStar.Reflection.Data.fst"; "FStar.Reflection.Basic.fst"; "FStar.Squash.fsti"; "FStar.Classical.fst";
  //                            "FStar.List.Tot.Base.fst"; "FStar.List.Tot.Properties.fst"; "FStar.List.Tot.fst"; "FStar.Char.fsti";
  //                            "FStar.String.fsti"; "FStar.Reflection.Syntax.fst"; "FStar.Reflection.Syntax.Lemmas.fst";
  //                            "FStar.Reflection.Formula.fst"; "FStar.Tactics.Types.fsti"; "FStar.Tactics.Result.fst";
  //                            "FStar.Tactics.Effect.fst"; "FStar.Tactics.Builtins.fst"; "FStar.Tactics.Derived.fst";
  //                            "FStar.Tactics.Logic.fst"; "FStar.Tactics.fst"] dsenv env in


  let env = {env with dsenv=dsenv} in (* VD: need to propagate add_mods to the dsenv in env *)

  let env = TcEnv.set_current_module env test_lid in
  tcenv_ref := Some env

let rec init () =
    match !tcenv_ref with
        | Some f -> f
        | _ -> init_once(); init()

let frag_of_text s = {frag_text=s; frag_line=1; frag_col=0}

let pars s =
    try
        let tcenv = init() in
        match parse (Fragment <| frag_of_text s) with
        | Term t ->
            ToSyntax.desugar_term tcenv.dsenv t
        | ParseError (e, msg, r) ->
            raise_error (e, msg) r
        | ASTFragment _ ->
            failwith "Impossible: parsing a Fragment always results in a Term"
    with
        | e when not ((Options.trace_error())) -> raise e

let tc' s =
    let tm = pars s in
    let tcenv = init() in
    let tcenv = {tcenv with top_level=false} in
    let tm, _, g = TcTerm.tc_tot_or_gtot_term tcenv tm in
    tm, g, tcenv

let tc s =
    let tm, _, _ = tc' s in
    tm

let tc_nbe s =
    let tm, g, tcenv = tc' s in
    Rel.force_trivial_guard tcenv g;
    tm

let pars_and_tc_fragment (s:string) =
    Options.set_option "trace_error" (Options.Bool true);
    let report () = FStar.Errors.report_all () |> ignore in
    try
        let tcenv = init() in
        let frag = frag_of_text s in
        try
          let test_mod', tcenv' = FStar.Universal.tc_one_fragment !test_mod_ref tcenv frag in
          test_mod_ref := test_mod';
          tcenv_ref := Some tcenv';
          let n = get_err_count () in
          if n <> 0
          then (report ();
                raise_err (Errors.Fatal_ErrorsReported, BU.format1 "%s errors were reported" (string_of_int n)))
        with e -> report(); raise_err (Errors.Fatal_TcOneFragmentFailed, "tc_one_fragment failed: " ^s)
    with
        | e when not ((Options.trace_error())) -> raise e

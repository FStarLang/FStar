﻿(*
   Copyright 2016 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Tests.Pars
open FStar
open FStar.Compiler
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Parser
open FStar.Compiler.Util
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
module BU = FStar.Compiler.Util
module D = FStar.Parser.Driver
module Rel = FStar.TypeChecker.Rel
module NBE = FStar.TypeChecker.NBE

let test_lid = Ident.lid_of_path ["Test"] Range.dummyRange
let tcenv_ref: ref (option TcEnv.env) = mk_ref None
let test_mod_ref = mk_ref (Some ({name=test_lid;
                                  declarations=[];
                                  is_interface=false}))

let parse_mod mod_name dsenv =
    match parse (Filename mod_name) with
    | ASTFragment (Inl m, _) ->
        let m, env'= ToSyntax.ast_modul_to_modul m dsenv in
        let env' , _ = DsEnv.prepare_module_or_interface false false env' (FStar.Ident.lid_of_path ["Test"] (FStar.Compiler.Range.dummyRange)) DsEnv.default_mii in
        env', m
    | ParseError (err, msg, r) ->
        raise (Error(err, msg, r, []))
    | ASTFragment (Inr _, _) ->
        let msg = BU.format1 "%s: expected a module\n" mod_name in
        raise_error (Errors.Fatal_ModuleExpected, msg) dummyRange
    | Term _ ->
        failwith "Impossible: parsing a Filename always results in an ASTFragment"

let add_mods mod_names dsenv env =
  List.fold_left (fun (dsenv,env) mod_name ->
      let dsenv, string_mod = parse_mod mod_name dsenv in
      let _mod, env = Tc.check_module env string_mod false in
      (dsenv, env)
  ) (dsenv,env) mod_names

let init_once () : unit =
  let solver = SMT.dummy in
  let env = TcEnv.initial_env
                FStar.Parser.Dep.empty_deps
                TcTerm.tc_term
                TcTerm.typeof_tot_or_gtot_term
                TcTerm.typeof_tot_or_gtot_term_fastpath
                TcTerm.universe_of
                Rel.teq_nosmt_force
                Rel.subtype_nosmt_force
                solver
                Const.prims_lid
                NBE.normalize_for_unit_test
                FStar.Universal.core_check
  in
  env.solver.init env;
  let dsenv, prims_mod = parse_mod (Options.prims()) (DsEnv.empty_env FStar.Parser.Dep.empty_deps) in
  let env = {env with dsenv=dsenv} in
  let _prims_mod, env = Tc.check_module env prims_mod false in
  // needed to run tests with chars
  // let dsenv, env = add_mods ["FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStar.Mul.fst"; "FStar.Squash.fsti";
  //                            "FStar.Classical.fst"; "FStar.Compiler.List.Tot.Base.fst"; "FStar.Compiler.List.Tot.Properties.fst"; "FStar.Compiler.List.Tot.fst";
  //                            "FStar.StrongExcludedMiddle.fst"; "FStar.Seq.Base.fst"; "FStar.Seq.Properties.fst"; "FStar.Seq.fst";
  //                            "FStar.BitVector.fst"; "FStar.Math.Lib.fst"; "FStar.Math.Lemmas.fst"; "FStar.UInt.fst"; "FStar.UInt32.fst";
  //                            "FStar.Char.fsti"; "FStar.String.fsti"] dsenv env in

  // only needed to test tatic normalization
  // let dsenv, env = add_mods ["FStar.Compiler.Range.fsti"; "FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStar.Reflection.Types.fsti"; "FStar.Order.fst";
  //                            "FStar.Reflection.Data.fst"; "FStar.Reflection.Basic.fst"; "FStar.Squash.fsti"; "FStar.Classical.fst";
  //                            "FStar.Compiler.List.Tot.Base.fst"; "FStar.Compiler.List.Tot.Properties.fst"; "FStar.Compiler.List.Tot.fst"; "FStar.Char.fsti";
  //                            "FStar.String.fsti"; "FStar.Reflection.Syntax.fst"; "FStar.Reflection.Syntax.Lemmas.fst";
  //                            "FStar.Reflection.Formula.fst"; "FStar.Tactics.Types.fsti"; "FStar.Tactics.Result.fst";
  //                            "FStar.Tactics.Effect.fst"; "FStar.Tactics.Builtins.fst"; "FStar.Tactics.Derived.fst";
  //                            "FStar.Tactics.Logic.fst"; "FStar.Tactics.fst"] dsenv env in


  let env = {env with dsenv=dsenv} in (* VD: need to propagate add_mods to the dsenv in env *)

  let env = TcEnv.set_current_module env test_lid in
  tcenv_ref := Some env

let _ =
  FStar.Main.setup_hooks();
  init_once()

let init () =
    match !tcenv_ref with
    | Some f -> f
    | _ ->
      failwith "Should have already been initialized by the top-level effect"

let frag_of_text s = {frag_fname=" input"; frag_text=s; frag_line=1; frag_col=0}

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
        | Error(err, msg, r, _ctx) when not <| FStar.Options.trace_error() ->
          if r = FStar.Compiler.Range.dummyRange
          then BU.print_string msg
          else BU.print2 "%s: %s\n" (FStar.Compiler.Range.string_of_range r) msg;
          exit 1

        | e when not ((Options.trace_error())) -> raise e

let tc' s =
    let tm = pars s in
    let tcenv = init() in
    let tcenv = {tcenv with top_level=false} in
    let tm, _, g = TcTerm.tc_tot_or_gtot_term tcenv tm in
    Rel.force_trivial_guard tcenv g;
    let tm = FStar.Syntax.Compress.deep_compress false tm in
    tm, tcenv

let tc s =
    let tm, _ = tc' s in
    tm

let tc_term tm =
    let tcenv = init() in
    let tcenv = {tcenv with top_level=false} in
    let tm, _, g = TcTerm.tc_tot_or_gtot_term tcenv tm in
    Rel.force_trivial_guard tcenv g;
    let tm = FStar.Syntax.Compress.deep_compress false tm in
    tm

let pars_and_tc_fragment (s:string) =
    Options.set_option "trace_error" (Options.Bool true);
    let report () = FStar.Errors.report_all () |> ignore in
    try
        let tcenv = init() in
        let frag = frag_of_text s in
        try
          let test_mod', tcenv' = FStar.Universal.tc_one_fragment !test_mod_ref tcenv (Inl frag) in
          test_mod_ref := test_mod';
          tcenv_ref := Some tcenv';
          let n = get_err_count () in
          if n <> 0
          then (report ();
                raise_err (Errors.Fatal_ErrorsReported, BU.format1 "%s errors were reported" (string_of_int n)))
        with e -> report(); raise_err (Errors.Fatal_TcOneFragmentFailed, "tc_one_fragment failed: " ^s)
    with
        | e when not ((Options.trace_error())) -> raise e

let test_hashes () =
  FStar.Main.process_args () |> ignore; //set options
  let _ = pars_and_tc_fragment "type unary_nat = | U0 | US of unary_nat" in
  let test_one_hash (n:int) =
    let rec aux n =
      if n = 0 then "U0"
      else "(US " ^ aux (n - 1) ^ ")"
    in
    let tm = tc (aux n) in
    let hc = FStar.Syntax.Hash.ext_hash_term tm in
    BU.print2 "Hash of unary %s is %s\n"
              (string_of_int n)
              (FStar.Hash.string_of_hash_code hc)
  in
  let rec aux (n:int) =
    if n = 0 then ()
    else (test_one_hash n; aux (n - 1))
  in
  aux 100;
  Options.init()


let parse_incremental_decls () =
  let source0 =
    "module Demo\n\
     let f x = match x with | Some x -> true | None -> false\n\
     let test y = if Some? y then f y else true\n\
     ```pulse\n\
     fn f() {}\n\
     ```\n\
     ```pulse\n\
     fn g() {}\n\
     ```\n\
     let something = more\n\
     let >< junk"
  in
  let source1 =
    "module Demo\n\
     let f x = match x with | Some x -> true | None -> false\n\
     let test y = if Some? y then f y else true\n\
     ```pulse\n\
     fn f() {}\n\
     ```\n\n\
     ```pulse\n\
     fn g() {}\n\
     ```\n\
     let something = more\n\
     let >< junk"
  in

  let open FStar.Parser.ParseIt in
  let input0 = Incremental { frag_fname = "Demo.fst";
                             frag_text = source0;
                             frag_line = 1;
                             frag_col = 0 } in
  let input1 = Incremental { frag_fname = "Demo.fst";
                             frag_text = source1;
                             frag_line = 1;
                             frag_col = 0 } in
  let open FStar.Compiler.Range in
  match parse input0, parse input1 with
  | IncrementalFragment (decls0, _, parse_err0),
    IncrementalFragment (decls1, _, parse_err1) -> (
      let check_range r l c =
          let p = start_of_range r in
          if line_of_pos p = l && col_of_pos p = c
          then ()
          else failwith (format4 "Incremental parsing failed: Expected syntax error at (%s, %s), got error at (%s, %s)"
                                 (string_of_int l)
                                 (string_of_int c)
                                 (string_of_int (line_of_pos p))
                                 (string_of_int (col_of_pos p)))
      in
      let _ =
        match parse_err0, parse_err1 with
        | None, _ ->
          failwith "Incremental parsing failed: Expected syntax error at (8, 6), got no error"
        | _, None ->
          failwith "Incremental parsing failed: Expected syntax error at (9, 6), got no error"
        | Some (_, _, rng0), Some (_, _, rng1)  ->
          check_range rng0 11 6;
          check_range rng1 12 6
      in
      match decls0, decls1 with
      | [d0;d1;d2;d3;d4;d5],
        [e0;e1;e2;e3;e4;e5] ->
        let open FStar.Parser.AST.Util in
        if List.forall2 (fun (x, _) (y, _) -> eq_decl x y) decls0 decls1
        then ()
        else (
          failwith ("Incremental parsing failed; unexpected change in a decl")
        )
      | _ -> failwith (format2 "Incremental parsing failed; expected 6 decls got %s and %s\n"
                              (string_of_int (List.length decls0))
                              (string_of_int (List.length decls1)))
      )


  | ParseError (code, message, range), _
  | _, ParseError (code, message, range) ->
      let msg =
        format2 "Incremental parsing failed: Syntax error @ %s: %s"
                (Range.string_of_range range)
                message
      in
      failwith msg

  | _ ->
      failwith "Incremental parsing failed: Unexpected output"

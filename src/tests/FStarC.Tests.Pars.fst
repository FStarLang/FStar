(*
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
module FStarC.Tests.Pars
open FStarC
open FStarC.Effect
open FStarC.Range
open FStarC.Parser
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Errors
open FStarC.TypeChecker.Env
open FStarC.Parser.ParseIt
open FStarC.Class.Show

module DsEnv = FStarC.Syntax.DsEnv
module TcEnv = FStarC.TypeChecker.Env
module SMT = FStarC.SMTEncoding.Solver
module Tc = FStarC.TypeChecker.Tc
module TcTerm = FStarC.TypeChecker.TcTerm
module ToSyntax = FStarC.ToSyntax.ToSyntax
module Rel = FStarC.TypeChecker.Rel
module NBE = FStarC.TypeChecker.NBE

let test_lid = Ident.lid_of_path ["Test"] Range.dummyRange
let tcenv_ref: ref (option TcEnv.env) = mk_ref None
let test_mod_ref = mk_ref (Some ({name=test_lid;
                                  declarations=[];
                                  is_interface=false}))

let parse_mod mod_name dsenv =
    match parse None (Filename mod_name) with
    | ASTFragment (Inl m, _) ->
        let m, env'= ToSyntax.ast_modul_to_modul m dsenv in
        let env' , _ = DsEnv.prepare_module_or_interface false false env' (FStarC.Ident.lid_of_path ["Test"] (FStarC.Range.dummyRange)) DsEnv.default_mii in
        env', m
    | ParseError (err, msg, r) ->
        raise (Error(err, msg, r, []))
    | ASTFragment (Inr _, _) ->
        let msg = Format.fmt1 "%s: expected a module\n" mod_name in
        raise_error0 Errors.Fatal_ModuleExpected msg
    | Term _ ->
        failwith "Impossible: parsing a Filename always results in an ASTFragment"

let add_mods mod_names dsenv env =
  List.fold_left (fun (dsenv,env) mod_name ->
      let dsenv, string_mod = parse_mod mod_name dsenv in
      let _mod, env = Tc.check_module env string_mod false in
      (dsenv, env)
  ) (dsenv,env) mod_names

let do_init () =
  let solver = SMT.dummy in
  let env = TcEnv.initial_env
                FStarC.Parser.Dep.empty_deps
                TcTerm.tc_term
                TcTerm.typeof_tot_or_gtot_term
                TcTerm.typeof_tot_or_gtot_term_fastpath
                TcTerm.universe_of
                Rel.teq_nosmt_force
                Rel.subtype_nosmt_force
                solver
                Const.prims_lid
                NBE.normalize_for_unit_test
                FStarC.Universal.core_check
  in
  env.solver.init env;
  let prelude_file =
    match Find.find_file "Prims.fst" with
    | Some f -> f
    | None -> failwith "Could not find Prims.fst: is FSTAR_LIB set?"
  in
  let dsenv, prims_mod =
    parse_mod prelude_file (DsEnv.empty_env Parser.Dep.empty_deps)
  in
  let env = {env with dsenv=dsenv} in
  let _prims_mod, env = Tc.check_module env prims_mod false in
  // needed to run tests with chars
  // let dsenv, env = add_mods ["FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStar.Mul.fst"; "FStar.Squash.fsti";
  //                            "FStar.Classical.fst"; "FStarC.List.Tot.Base.fst"; "FStarC.List.Tot.Properties.fst"; "FStarC.List.Tot.fst";
  //                            "FStar.StrongExcludedMiddle.fst"; "FStar.Seq.Base.fst"; "FStar.Seq.Properties.fst"; "FStar.Seq.fst";
  //                            "FStar.BitVector.fst"; "FStar.Math.Lib.fst"; "FStar.Math.Lemmas.fst"; "FStar.UInt.fst"; "FStar.UInt32.fst";
  //                            "FStar.Char.fsti"; "FStar.String.fsti"] dsenv env in

  // only needed to test tatic normalization
  // let dsenv, env = add_mods ["FStarC.Range.fsti"; "FStar.Pervasives.Native.fst"; "FStar.Pervasives.fst"; "FStarC.Reflection.Types.fsti"; "FStar.Order.fst";
  //                            "FStarC.Reflection.Data.fst"; "FStarC.Reflection.Basic.fst"; "FStar.Squash.fsti"; "FStar.Classical.fst";
  //                            "FStarC.List.Tot.Base.fst"; "FStarC.List.Tot.Properties.fst"; "FStarC.List.Tot.fst"; "FStar.Char.fsti";
  //                            "FStar.String.fsti"; "FStarC.Reflection.Syntax.fst"; "FStarC.Reflection.Syntax.Lemmas.fst";
  //                            "FStarC.Reflection.Formula.fst"; "FStarC.Tactics.Types.fsti"; "FStarC.Tactics.Result.fst";
  //                            "FStarC.Tactics.Effect.fst"; "FStarC.Tactics.Builtins.fst"; "FStarC.Tactics.Derived.fst";
  //                            "FStarC.Tactics.Logic.fst"; "FStarC.Tactics.fst"] dsenv env in


  let env = {env with dsenv=dsenv} in (* VD: need to propagate add_mods to the dsenv in env *)

  (* open Prims explicitly, we're not getting the prelude inserted *)
  let env = { env with dsenv = DsEnv.push_namespace env.dsenv Const.prims_lid Unrestricted } in

  let env = TcEnv.set_current_module env test_lid in
  tcenv_ref := Some env

let init () =
  match !tcenv_ref with
  | Some f -> f
  | _ ->
    failwith "Should have already been initialized by the top-level effect"

let frag_of_text s = {frag_fname=" input"; frag_text=s; frag_line=1; frag_col=0}

let pars s =
    try
        let tcenv = init() in
        match parse None (Fragment <| frag_of_text s) with
        | Term t ->
            ToSyntax.desugar_term tcenv.dsenv t
        | ParseError (e, msg, r) ->
            raise_error r e msg
        | ASTFragment _ ->
            failwith "Impossible: parsing a Fragment always results in a Term"
    with
        | Error(err, msg, r, _ctx) when not <| FStarC.Options.trace_error() ->
          if r = FStarC.Range.dummyRange
          then Format.print_string (Errors.rendermsg msg)
          else Format.print2 "%s: %s\n" (FStarC.Range.string_of_range r) (Errors.rendermsg msg);
          exit 1

        | e when not ((Options.trace_error())) -> raise e

let tc' s =
    let tm = pars s in
    let tcenv = init() in
    (* We set phase1=true to allow the typechecker to insert
    coercions. *)
    let tcenv = {tcenv with phase1=true; top_level=false} in
    let tm, _, g = TcTerm.tc_tot_or_gtot_term tcenv tm in
    Rel.force_trivial_guard tcenv g;
    let tm = FStarC.Syntax.Compress.deep_compress false false tm in
    tm, tcenv

let tc s =
    let tm, _ = tc' s in
    tm

let tc_term tm =
    let tcenv = init() in
    let tcenv = {tcenv with top_level=false} in
    let tm, _, g = TcTerm.tc_tot_or_gtot_term tcenv tm in
    Rel.force_trivial_guard tcenv g;
    let tm = FStarC.Syntax.Compress.deep_compress false false tm in
    tm

let pars_and_tc_fragment (s:string) =
  Errors.with_ctx ("pars_and_tc_fragment " ^ s) fun () ->
  let tcenv = init() in
  let frag = frag_of_text s in
  let test_mod', tcenv', _ = FStarC.Universal.tc_one_fragment !test_mod_ref tcenv (Inl (frag, [])) in
  test_mod_ref := test_mod';
  tcenv_ref := Some tcenv'

let test_hashes () =
  Options.parse_cmd_line () |> ignore; //set options
  let _ = pars_and_tc_fragment "type unary_nat = | U0 | US of unary_nat" in
  let test_one_hash (n:int) =
    let rec aux n =
      if n = 0 then "U0"
      else "(US " ^ aux (n - 1) ^ ")"
    in
    let tm = tc (aux n) in
    let hc = FStarC.Syntax.Hash.ext_hash_term tm in
    Format.print2 "Hash of unary %s is %s\n"
              (show n)
              (FStarC.Hash.string_of_hash_code hc)
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

  let open FStarC.Parser.ParseIt in
  let input0 = Incremental { frag_fname = "Demo.fst";
                             frag_text = source0;
                             frag_line = 1;
                             frag_col = 0 } in
  let input1 = Incremental { frag_fname = "Demo.fst";
                             frag_text = source1;
                             frag_line = 1;
                             frag_col = 0 } in
  let open FStarC.Range in
  match parse None input0, parse None input1 with
  | IncrementalFragment (decls0, _, parse_err0),
    IncrementalFragment (decls1, _, parse_err1) -> (
      let check_range r l c =
          let p = start_of_range r in
          if line_of_pos p = l && col_of_pos p = c
          then ()
          else failwith (Format.fmt4 "Incremental parsing failed: Expected syntax error at (%s, %s), got error at (%s, %s)"
                                 (show l)
                                 (show c)
                                 (show (line_of_pos p))
                                 (show (col_of_pos p)))
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
        let open FStarC.Parser.AST.Diff in
        if List.forall2 (fun (x, _) (y, _) -> eq_decl x y) decls0 decls1
        then ()
        else (
          failwith ("Incremental parsing failed; unexpected change in a decl")
        )
      | _ -> failwith (Format.fmt2 "Incremental parsing failed; expected 6 decls got %s and %s\n"
                              (show (List.length decls0))
                              (show (List.length decls1)))
      )


  | ParseError (code, message, range), _
  | _, ParseError (code, message, range) ->
      let msg =
        Format.fmt2 "Incremental parsing failed: Syntax error @ %s: %s"
                (Range.string_of_range range)
                (Errors.rendermsg message) // FIXME
      in
      failwith msg

  | _ ->
      failwith "Incremental parsing failed: Unexpected output"


open FStarC.Class.Show

let parse_incremental_decls_use_lang () =
  let source0 =
    "module Demo\n\
     let x = 0\n\
     #lang-somelang\n\
     val f : t\n\
     let g x = f x\n\
     #restart-solver"
  in
  FStarC.Parser.AST.Util.register_extension_lang_parser "somelang" FStarC.Parser.ParseIt.parse_fstar_incrementally;
  let open FStarC.Parser.ParseIt in
  let input0 = Incremental { frag_fname = "Demo.fst";
                             frag_text = source0;
                             frag_line = 1;
                             frag_col = 0 } in
  let open FStarC.Range in
  match parse None input0 with
  | IncrementalFragment (decls0, _, parse_err0) -> (
      let _ =
        match parse_err0 with
        | None -> ()
        | Some _ ->
          failwith "Incremental parsing failed: ..."
      in
      let open FStarC.Parser.AST in
      let ds = List.map fst decls0 in
      match ds with
      | [{d=TopLevelModule _}; {d=TopLevelLet _}; {d=UseLangDecls _}; {d=Val _}; {d=TopLevelLet _}; {d=Pragma _}] -> ()
      | _ ->
       failwith ("Incremental parsing failed; unexpected decls: " ^ show ds)
      )


  | ParseError (code, message, range) ->
      let msg =
        Format.fmt2 "Incremental parsing failed: Syntax error @ %s: %s"
                (Range.string_of_range range)
                (Errors.rendermsg message) // FIXME
      in
      failwith msg

  | _ ->
      failwith "Incremental parsing failed: Unexpected output"

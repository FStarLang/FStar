(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
#light "off"

//Top-level invocations into the universal type-checker FStar.TypeChecker
module FStar.Universal
open FStar.All
open FStar
open FStar.Errors
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Dependencies

(* Module abbreviations for the universal type-checker  *)
module DsEnv   = FStar.ToSyntax.Env
module TcEnv   = FStar.TypeChecker.Env
module Syntax  = FStar.Syntax.Syntax
module Util    = FStar.Syntax.Util
module Desugar = FStar.ToSyntax.ToSyntax
module SMT     = FStar.SMTEncoding.Solver
module Const   = FStar.Syntax.Const
module Tc      = FStar.TypeChecker.Tc
module TcTerm  = FStar.TypeChecker.TcTerm
module BU      = FStar.Util

let module_or_interface_name m = m.is_interface, m.name

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:DsEnv.env) (pre_fn: option<string>) (fn:string)
  : DsEnv.env
  * list<Syntax.modul> =
  let ast, _ = Parser.Driver.parse_file fn in
  let env, ast = match pre_fn with
    | None ->
        env, ast
    | Some pre_fn ->
        let pre_ast, _ = Parser.Driver.parse_file pre_fn in
        match pre_ast, ast with
        | [ Parser.AST.Interface (lid1, decls1, _) ], [ Parser.AST.Module (lid2, decls2) ]
          when Ident.lid_equals lid1 lid2 ->
          let env = FStar.ToSyntax.Interleave.initialize_interface lid1 decls1 env in
          let env, ast = FStar.ToSyntax.Interleave.interleave_module env (List.hd ast) true in
          env, [ast]
        | _ ->
            raise (Err ("mismatch between pre-module and module\n"))
  in
//  if fn = "test.fst"
//  then printfn "<front end>\n%s\n</front end>\n" ast (ast |> List.map
//        (fun m ->
//            let doc = FStar.Parser.ToDocument.modul_to_document m in
//            FStar.Pprint.pretty_string 0.8 100 doc)
//       |>  String.concat "\n\n");
  Desugar.desugar_file env ast


(***********************************************************************)
(* Checking Prims.fst                                                  *)
(***********************************************************************)
let tc_prims () : (Syntax.modul * int)
                  * DsEnv.env
                  * TcEnv.env =
  let solver = if Options.lax() then SMT.dummy else {SMT.solver with preprocess=FStar.Tactics.Interpreter.preprocess} in
  let env = TcEnv.initial_env TcTerm.type_of_tot_term TcTerm.universe_of solver Const.prims_lid in
  env.solver.init env;
  let prims_filename = Options.prims () in
  let dsenv, prims_mod = parse (DsEnv.empty_env ()) None prims_filename in
  let (prims_mod, env), elapsed_time =
    record_time (fun () -> Tc.check_module env (List.hd prims_mod)) in
  (prims_mod, elapsed_time), dsenv, env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
let tc_one_fragment curmod dsenv (env:TcEnv.env) (frag, is_interface_dependence) =
  try
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty ->
      Some (curmod, dsenv, env)

    | Parser.Driver.Modul ast_modul ->
        (* It may seem surprising that this function, whose name indicates that
        it type-checks a fragment, can actually parse an entire module.
        Actually, this is an abuse, and just means that we're type-checking the
        first chunk. *)
      let ds_env, ast_modul = FStar.ToSyntax.Interleave.interleave_module dsenv ast_modul false in
      let dsenv, modul = Desugar.desugar_partial_modul curmod dsenv ast_modul in
      let dsenv = if is_interface_dependence then FStar.ToSyntax.Env.set_iface dsenv false else dsenv in
      let env = match curmod with
        | Some modul ->
            (* Same-module is only allowed when editing a fst with an fsti,
             * because we sent the interface as the first chunk. *)
            if Parser.Dep.lowercase_module_name (List.hd (Options.file_list ())) <>
              String.lowercase (string_of_lid modul.name)
            then
              raise (Err("Interactive mode only supports a single module at the top-level"))
            else
              env
        | None ->
            env
      in
      let modul, _, env = if DsEnv.syntax_only dsenv then (modul, [], env)
                          else Tc.tc_partial_modul env modul in
      Some (Some modul, dsenv, env)

    | Parser.Driver.Decls ast_decls ->
      let dsenv, ast_decls_l =
            BU.fold_map FStar.ToSyntax.Interleave.prefix_with_interface_decls
                        dsenv
                        ast_decls in
      let dsenv, decls = Desugar.desugar_decls dsenv (List.flatten ast_decls_l) in
      match curmod with
        | None -> FStar.Util.print_error "fragment without an enclosing module"; exit 1
        | Some modul ->
            let modul, _, env  = if DsEnv.syntax_only dsenv then (modul, [], env)
                                 else Tc.tc_more_partial_modul env modul decls in
            Some (Some modul, dsenv, env)

    with
      | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,r)];
          None
      | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,Range.dummyRange)];
          None
      | e when not ((Options.trace_error())) -> raise e

let load_interface_decls (dsenv,env) interface_file_name : DsEnv.env * FStar.TypeChecker.Env.env =
  try
    let r = FStar.Parser.ParseIt.parse (Inl interface_file_name) in
    match r with
    | Inl (Inl [FStar.Parser.AST.Interface(l, decls, _)], _) ->
      FStar.ToSyntax.Interleave.initialize_interface l decls dsenv, env
    | Inl _ ->
      raise (FStar.Errors.Err(BU.format1 "Unexpected result from parsing %s; expected a single interface"
                               interface_file_name))
    | Inr (err, rng) ->
      raise (FStar.Errors.Error(err, rng))
  with
      | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,r)];
          dsenv, env
      | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,Range.dummyRange)];
          dsenv, env
      | e when not ((Options.trace_error())) -> raise e

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)
let tc_one_file dsenv env pre_fn fn : list<(Syntax.modul * int)> //each module and its elapsed checking time
                                    * DsEnv.env
                                    * TcEnv.env  =
  let dsenv, fmods = parse dsenv pre_fn fn in
  let check_mods () =
      let env, all_mods =
          fmods |> List.fold_left (fun (env, all_mods) m ->
                    let (m, env), elapsed_ms =
                        FStar.Util.record_time (fun () -> Tc.check_module env m) in
                    env, (m, elapsed_ms)::all_mods) (env, []) in
      List.rev all_mods, dsenv, env
  in
  match fmods with
  | [m] when (Options.should_verify m.name.str //if we're verifying this module
              && (FStar.Options.record_hints() //and if we're recording or using hints
                  || FStar.Options.use_hints())) ->
    SMT.with_hints_db (FStar.Parser.ParseIt.find_file fn) check_mods
  | _ -> check_mods() //don't add a hints file for modules that are not actually verified

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  FStar.Util.get_file_extension intf = "fsti" && FStar.Util.get_file_extension impl = "fst"

let pop_context env msg =
    DsEnv.pop () |> ignore;
    TcEnv.pop env msg |> ignore;
    env.solver.refresh()

let push_context (dsenv, env) msg =
    let dsenv = DsEnv.push dsenv in
    let env = TcEnv.push env msg in
    (dsenv, env)

type uenv = DsEnv.env * env

let tc_one_file_from_remaining (remaining:list<string>) (uenv:uenv) = //:(string list * (modul* int) list * uenv) =
  let dsenv, env = uenv in
  let remaining, (nmods, dsenv, env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          remaining, tc_one_file dsenv env (Some intf) impl
        | intf_or_impl :: remaining ->
          remaining, tc_one_file dsenv env None intf_or_impl
        | [] -> [], ([], dsenv, env)
  in
  remaining, nmods, (dsenv, env)

let rec tc_fold_interleave (acc:list<(modul * int)> * uenv) (remaining:list<string>) =
  match remaining with
    | [] -> acc
    | _  ->
      let mods, uenv = acc in
      let remaining, nmods, (dsenv, env) = tc_one_file_from_remaining remaining uenv in
      tc_fold_interleave (mods@nmods, (dsenv, env)) remaining

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc_no_prims dsenv env filenames =
  let all_mods, (dsenv, env) = tc_fold_interleave ([], (dsenv, env)) filenames in
  if Options.interactive()
  && FStar.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, dsenv, env

let batch_mode_tc filenames =
  let prims_mod, dsenv, env = tc_prims () in
  if not (Options.explicit_deps ()) && Options.debug_any () then begin
    FStar.Util.print_endline "Auto-deps kicked in; here's some info.";
    FStar.Util.print1 "Here's the list of filenames we will process: %s\n"
      (String.concat " " filenames);
    FStar.Util.print1 "Here's the list of modules we will verify: %s\n"
      (String.concat " " (Options.verify_module ()))
  end;
  let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames in
  prims_mod :: all_mods, dsenv, env

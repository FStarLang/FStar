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
open FStar
open FStar.Errors
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Dependencies
open FStar.Interactive

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

let module_or_interface_name m = m.is_interface, m.name

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:DsEnv.env) (pre_fn: option<string>) (fn:string)
  : DsEnv.env
  * list<Syntax.modul> =
  let ast, _ = Parser.Driver.parse_file fn in
  let ast = match pre_fn with
    | None ->
        ast
    | Some pre_fn ->
        let pre_ast, _ = Parser.Driver.parse_file pre_fn in
        match pre_ast, ast with
        | [ Parser.AST.Interface (lid1, decls1, _) ], [ Parser.AST.Module (lid2, decls2) ]
          when Ident.lid_equals lid1 lid2 ->
            [ Parser.AST.Module (lid1, FStar.Parser.Interleave.interleave decls1 decls2) ]
        | _ ->
            raise (Err ("mismatch between pre-module and module\n"))
  in
  Desugar.desugar_file env ast


(***********************************************************************)
(* Checking Prims.fst                                                  *)
(***********************************************************************)
let tc_prims () : (Syntax.modul * int)
                  * DsEnv.env
                  * TcEnv.env =
  let solver = if Options.lax() then SMT.dummy else SMT.solver in
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
let tc_one_fragment curmod dsenv (env:TcEnv.env) frag =
  try
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty ->
      Some (curmod, dsenv, env)

    | Parser.Driver.Modul ast_modul ->
      let dsenv, modul = Desugar.desugar_partial_modul curmod dsenv ast_modul in
      let env = match curmod with
          | None -> env
          | Some _ -> raise (Err("Interactive mode only supports a single module at the top-level")) in
      let modul, _, env = Tc.tc_partial_modul env modul in
      Some (Some modul, dsenv, env)

    | Parser.Driver.Decls ast_decls ->
      let dsenv, decls = Desugar.desugar_decls dsenv ast_decls in
      match curmod with
        | None -> FStar.Util.print_error "fragment without an enclosing module"; exit 1
        | Some modul ->
            let modul, _, env  = Tc.tc_more_partial_modul env modul decls in
            Some (Some modul, dsenv, env)

    with
      | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,r)];
          None
      | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,Range.dummyRange)];
          None
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
    SMT.with_hints_db fn check_mods
  | _ -> check_mods() //don't add a hints file for modules that are not actually verified

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  FStar.Util.get_file_extension intf = "fsti" && FStar.Util.get_file_extension impl = "fst"

let pop_context (dsenv, env) msg =
    DsEnv.pop dsenv |> ignore;
    TcEnv.pop env msg |> ignore;
    env.solver.refresh()

let push_context (dsenv, env) msg =
    let dsenv = DsEnv.push dsenv in
    let env = TcEnv.push env msg in
    (dsenv, env)

let tc_one_file_and_intf (intf:option<string>) (impl:string) (dsenv:DsEnv.env) (env:env) = //:(modul * int) list * Parser.Env.env * env =
  Syntax.reset_gensym ();
  match intf with
    | None -> //no interface; easy
      tc_one_file dsenv env None impl
    | Some _ when ((Options.codegen()) <> None) ->
        if not (Options.lax())
        then raise (Err "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately");
        tc_one_file dsenv env intf impl
    | Some iname ->
        if Options.debug_any () then
        FStar.Util.print1 "Interleaving iface+module: %s\n" iname;
        let caption = "interface: " ^ iname in
        //push a new solving context, so that we can blow away implementation details below
        let dsenv', env' = push_context (dsenv, env) caption in
        let _, dsenv', env' = tc_one_file dsenv' env' intf impl in //check the impl and interface together, if any
        //discard the impl and check the interface alone for the rest of the program
        let _ = pop_context (dsenv', env') caption in
        tc_one_file dsenv env None iname //check the interface alone

type uenv = DsEnv.env * env

let tc_one_file_from_remaining (remaining:list<string>) (uenv:uenv) = //:(string list * (modul* int) list * uenv) =
  let dsenv, env = uenv in
  let remaining, (nmods, dsenv, env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          remaining, tc_one_file_and_intf (Some intf) impl dsenv env
        | intf_or_impl :: remaining ->
          remaining, tc_one_file_and_intf None intf_or_impl dsenv env
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

(******************************************************************************)
(* Building an instance of the type-checker to be run in the interactive loop *)
(******************************************************************************)
let tc_prims_interactive () = //:uenv =
  let _, dsenv, env = tc_prims () in
  (dsenv, env)

let tc_one_file_interactive (remaining:list<string>) (uenv:uenv) = //:((string option * string) * uenv * modul option * string list) =
  let dsenv, env = uenv in
  let (intf, impl), dsenv, env, remaining =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let _, dsenv, env = tc_one_file_and_intf (Some intf) impl dsenv env in
          (Some intf, impl), dsenv, env, remaining
        | intf_or_impl :: remaining ->
          let _, dsenv, env = tc_one_file_and_intf None intf_or_impl dsenv env in
          (None, intf_or_impl), dsenv, env, remaining
        | [] -> failwith "Impossible"
  in
  (intf, impl), (dsenv, env), None, remaining

let interactive_tc : interactive_tc<(DsEnv.env * TcEnv.env), option<Syntax.modul>> =
    let pop (dsenv, env) msg =
          pop_context (dsenv, env) msg;
          Options.pop() in

    let push (dsenv, env) lax restore_cmd_line_options msg =
          let env = { env with lax = lax } in
          let res = push_context (dsenv, env) msg in
          Options.push();
          if restore_cmd_line_options then Options.restore_cmd_line_options false |> ignore;
          res in

    let mark (dsenv, env) =
        let dsenv = DsEnv.mark dsenv in
        let env = TcEnv.mark env in
        Options.push();
        dsenv, env in

    let reset_mark (dsenv, env) =
        let dsenv = DsEnv.reset_mark dsenv in
        let env = TcEnv.reset_mark env in
        Options.pop();
        dsenv, env in

    let cleanup (dsenv, env) = TcEnv.cleanup_interactive env in

    let commit_mark (dsenv, env) =
        let dsenv = DsEnv.commit_mark dsenv in
        let env = TcEnv.commit_mark env in
        dsenv, env in

    let check_frag (dsenv, (env:TcEnv.env)) curmod text =
        try
            match tc_one_fragment curmod dsenv env text with
                | Some (m, dsenv, env) ->
                  Some (m, (dsenv, env), FStar.Errors.get_err_count())
                | _ -> None
        with
            | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
              FStar.TypeChecker.Err.add_errors env [(msg, r)];
              None

            | FStar.Errors.Err msg when not ((Options.trace_error())) ->
              FStar.TypeChecker.Err.add_errors env [(msg, FStar.TypeChecker.Env.get_range env)];
              None in

    let report_fail () =
        FStar.Errors.report_all() |> ignore;
        FStar.Errors.num_errs := 0 in

    { pop = pop;
      push = push;
      mark = mark;
      reset_mark = reset_mark;
      commit_mark = commit_mark;
      check_frag = check_frag;
      report_fail = report_fail;
      tc_prims = tc_prims_interactive;
      tc_one_file = tc_one_file_interactive;
      cleanup = cleanup }

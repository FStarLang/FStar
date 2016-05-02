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
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Dependences
open FStar.Interactive

(* Module abbreviations for the universal type-checker  *)
module DsEnv   = FStar.Parser.Env 
module TcEnv   = FStar.TypeChecker.Env
module Syntax  = FStar.Syntax.Syntax
module Util    = FStar.Syntax.Util
module Desugar = FStar.Parser.ToSyntax
module SMT     = FStar.SMTEncoding.Encode
module Const   = FStar.Syntax.Const
module Tc      = FStar.TypeChecker.Tc

let module_or_interface_name m = m.is_interface, m.name

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:DsEnv.env) (pre_fn: option<string>) (fn:string) 
  : DsEnv.env
  * list<Syntax.modul> =
  let ast = Parser.Driver.parse_file fn in
  let ast = match pre_fn with
    | None ->
        ast
    | Some pre_fn ->
        let pre_ast = Parser.Driver.parse_file pre_fn in
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
let tc_prims () : Syntax.modul
                  * DsEnv.env
                  * TcEnv.env =
  let solver = if !Options.verify then SMT.solver else SMT.dummy in
  let env = TcEnv.initial_env Tc.type_of solver Const.prims_lid in
  env.solver.init env;
  let p = Options.prims () in
  let dsenv, prims_mod = parse (DsEnv.empty_env ()) None p in
  let prims_mod, env = Tc.check_module env (List.hd prims_mod) in
  prims_mod, dsenv, env

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
          | Some _ -> raise (Syntax.Err("Interactive mode only supports a single module at the top-level")) in
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
      | Syntax.Error(msg, r) when not (!Options.trace_error) ->
          TypeChecker.Errors.add_errors env [(msg,r)];
          None
      | Syntax.Err msg when not (!Options.trace_error) ->
          TypeChecker.Errors.add_errors env [(msg,Range.dummyRange)];
          None
      | e when not (!Options.trace_error) -> raise e

(******************************************************************************)
(* Building an instance of the type-checker to be run in the interactive loop *)
(******************************************************************************)
let interactive_tc : interactive_tc<(DsEnv.env * TcEnv.env), option<Syntax.modul>> = 
    let pop (dsenv, env) msg = 
          DsEnv.pop dsenv |> ignore;
          TcEnv.pop env msg |> ignore;
          env.solver.refresh();
          Options.restore_cmd_line_options() |> ignore in

    let push (dsenv, env) msg = 
          let dsenv = DsEnv.push dsenv in
          let env = TcEnv.push env msg in
          (dsenv, env) in

    let mark (dsenv, env) =
        let dsenv = DsEnv.mark dsenv in
        let env = TcEnv.mark env in
        dsenv, env in

    let reset_mark (dsenv, env) =
        let dsenv = DsEnv.reset_mark dsenv in
        let env = TcEnv.reset_mark env in
        dsenv, env in

    let commit_mark (dsenv, env) =
        let dsenv = DsEnv.commit_mark dsenv in
        let env = TcEnv.commit_mark env in
        dsenv, env in

    let check_frag (dsenv, (env:TcEnv.env)) curmod text =  
        try 
            match tc_one_fragment curmod dsenv env text with 
                | Some (m, dsenv, env) -> 
                  Some (m, (dsenv, env), FStar.TypeChecker.Errors.get_err_count())
                | _ -> None
        with 
            | FStar.Syntax.Syntax.Error(msg, r) when not (!Options.trace_error) ->
              FStar.TypeChecker.Errors.add_errors env [(msg, r)];
              None
              
            | FStar.Syntax.Syntax.Err msg when not (!Options.trace_error) ->
              FStar.TypeChecker.Errors.add_errors env [(msg, FStar.TypeChecker.Env.get_range env)];
              None in

    let report_fail () = 
        TypeChecker.Errors.report_all() |> ignore;
        TypeChecker.Errors.num_errs := 0 in

    { pop = pop; 
      push = push;
      mark = mark;
      reset_mark = reset_mark;
      commit_mark = commit_mark;
      check_frag = check_frag;
      report_fail = report_fail}

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)
let tc_one_file dsenv env pre_fn fn : list<Syntax.modul>
                               * DsEnv.env
                               * TcEnv.env  =
  let dsenv, fmods = parse dsenv pre_fn fn in
  let deps = 
    if !Options.explicit_deps then
      (* dummy value; we don't use cached fuel traces when `--explicit_deps` is specified; see `FStar.SMTEncoding.ErrorReporting.initialize_fuel_trace` for more info. *)
      []
    else begin
      (* use the auto-deps facitity to produce a list of dependencies for `fn` *)
      let g, _ = Parser.Dep.collect [fn] in
      match
        List.filter
          (fun p ->
            fst p = fn)
          g
      with
      | [ (_, l) ] ->
        l
      | _ ->
        raise <| Util.Failure (format1 "Internal error: expected to find exactly one entry for %s in dependency graph" fn)
    end
  in
  FStar.SMTEncoding.ErrorReporting.initialize_fuel_trace fn deps;
  let env, all_mods =
    fmods |> List.fold_left (fun (env, all_mods) m ->
                            let m, env = Tc.check_module env m in
                            env, m::all_mods) (env, []) in
  // for the moment, there should be no need to trap exceptions to finalize the fuel trace logic. nothing is done if an error occurs.
  FStar.SMTEncoding.ErrorReporting.finalize_fuel_trace fn deps;
  List.rev all_mods, dsenv, env

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  FStar.Util.get_file_extension intf = "fsti" && FStar.Util.get_file_extension impl = "fst"

let rec tc_fold_interleave acc remaining =
  let move intf impl remaining =
    Syntax.reset_gensym ();
    let all_mods, dsenv, env = acc in
    let ms, dsenv, env = match intf with 
        | None -> //no interface; easy
          tc_one_file dsenv env intf impl 

        | Some _ when (!Options.codegen <> None) -> 
          if !Options.verify
          then raise (Err "Verification and code generation are no supported together with partial modules (i.e, *.fsti); use --lax to extract code separately");
          tc_one_file dsenv env intf impl

        | Some iname -> 
          let caption = "interface: " ^ iname in
          //push a new solving context, so that we can blow away implementation details below
          let dsenv', env' = interactive_tc.push (dsenv, env) caption in
          let _, dsenv', env' = tc_one_file dsenv' env' intf impl in //check the impl and interface together, if any
          //discard the impl and check the interface alone for the rest of the program
          let _ = interactive_tc.pop (dsenv', env') caption in
          tc_one_file dsenv env None iname in //check the interface alone
    let acc = all_mods @ ms, dsenv, env in
    tc_fold_interleave acc remaining
  in

  match remaining with
  | intf :: impl :: remaining when needs_interleaving intf impl ->
      move (Some intf) impl remaining
  | intf_or_impl :: remaining ->
      move None intf_or_impl remaining
  | [] ->
      acc

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc_no_prims dsenv env filenames =
  let all_mods, dsenv, env = tc_fold_interleave ([], dsenv, env) filenames in
  if !Options.interactive && FStar.TypeChecker.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, dsenv, env

let batch_mode_tc filenames =
  let prims_mod, dsenv, env = tc_prims () in
  let filenames, admit_fsi = find_deps_if_needed filenames in
  let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames in
  prims_mod :: all_mods, dsenv, env


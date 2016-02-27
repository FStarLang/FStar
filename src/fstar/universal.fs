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
let parse (env:DsEnv.env) (fn:string) : DsEnv.env  
                                          * list<Syntax.modul> =
  let ast = Parser.Driver.parse_file fn in
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
  let dsenv, prims_mod = parse (DsEnv.empty_env()) p in
  let prims_mod, env = Tc.check_module env (List.hd prims_mod) in
  prims_mod, dsenv, env

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)
let tc_one_file dsenv env fn : list<Syntax.modul>
                               * DsEnv.env  
                               * TcEnv.env  =
  let dsenv, fmods = parse dsenv fn in
  let env, all_mods =
    fmods |> List.fold_left (fun (env, all_mods) m ->
                            let m, env = Tc.check_module env m in
                            env, m::all_mods) (env, []) in
  List.rev all_mods, dsenv, env

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc_no_prims dsenv env filenames =
  let all_mods, dsenv, env =
    filenames |> List.fold_left (fun (all_mods, dsenv, env) f ->
                                Syntax.reset_gensym();
                                let ms, dsenv, env= tc_one_file dsenv env f in
                                all_mods@ms, dsenv, env)
                                ([], dsenv, env) in
  if !Options.interactive && FStar.TypeChecker.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, dsenv, env

let batch_mode_tc filenames =
  let prims_mod, dsenv, env = tc_prims () in
  let filenames, admit_fsi = find_deps_if_needed filenames in
  let all_mods, dsenv, env = batch_mode_tc_no_prims dsenv env filenames in
  prims_mod :: all_mods, dsenv, env

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
          | Some _ -> raise (Absyn.Syntax.Err("Interactive mode only supports a single module at the top-level")) in
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
      | Syntax.Error(msg, r) ->
          TypeChecker.Errors.add_errors env [(msg,r)];
          None
      | Syntax.Err msg ->
          TypeChecker.Errors.add_errors env [(msg,Range.dummyRange)];
          None
      | e -> raise e

(******************************************************************************)
(* Building an instance of the type-checker to be run in the interactive loop *)
(******************************************************************************)
let interactive_tc : interactive_tc<(DsEnv.env * TcEnv.env), option<Syntax.modul>> = 
    let pop (dsenv, env) msg = 
          DsEnv.pop dsenv |> ignore;
          TcEnv.pop env msg |> ignore;
          env.solver.refresh();
          Options.reset_options() |> ignore in

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
        match tc_one_fragment curmod dsenv env text with 
            | Some (m, dsenv, env) -> 
              Some (m, (dsenv, env), FStar.TypeChecker.Errors.get_err_count())
            | _ -> None in

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

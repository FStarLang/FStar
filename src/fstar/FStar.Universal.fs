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
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Errors
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.TypeChecker.Env
open FStar.Dependencies

(* Module abbreviations for the universal type-checker  *)
module DsEnv   = FStar.ToSyntax.Env
module TcEnv   = FStar.TypeChecker.Env
module Syntax  = FStar.Syntax.Syntax
module Util    = FStar.Syntax.Util
module Desugar = FStar.ToSyntax.ToSyntax
module SMT     = FStar.SMTEncoding.Solver
module Const   = FStar.Parser.Const
module Tc      = FStar.TypeChecker.Tc
module TcTerm  = FStar.TypeChecker.TcTerm
module BU      = FStar.Util

let module_or_interface_name m = m.is_interface, m.name

let user_tactics_modules = Tc.user_tactics_modules

let with_tcenv  (env:TcEnv.env) (f:DsEnv.withenv<'a>) =
    let a, dsenv = f env.dsenv in
    a, ({env with dsenv=dsenv})

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:TcEnv.env) (pre_fn: option<string>) (fn:string)
  : Syntax.modul
  * TcEnv.env =
  let ast, _ = Parser.Driver.parse_file fn in
  let ast, env = match pre_fn with
    | None ->
        ast, env
    | Some pre_fn ->
        let pre_ast, _ = Parser.Driver.parse_file pre_fn in
        match pre_ast, ast with
        | Parser.AST.Interface (lid1, decls1, _), Parser.AST.Module (lid2, decls2)
          when Ident.lid_equals lid1 lid2 ->
          let _, env = with_tcenv env <| FStar.ToSyntax.Interleave.initialize_interface lid1 decls1 in
          with_tcenv env <| FStar.ToSyntax.Interleave.interleave_module ast true
        | _ ->
            raise (Err ("mismatch between pre-module and module\n"))
  in
  with_tcenv env <| Desugar.ast_modul_to_modul ast

(***********************************************************************)
(* Initialize a clean environment                                      *)
(***********************************************************************)
let init_env () : TcEnv.env =
  let solver = if Options.lax() then SMT.dummy else {SMT.solver with preprocess=FStar.Tactics.Interpreter.preprocess} in
  let env = TcEnv.initial_env TcTerm.tc_term TcTerm.type_of_tot_term TcTerm.universe_of solver Const.prims_lid in
  (* Set up some tactics callbacks *)
  let env = { env with synth = FStar.Tactics.Interpreter.synth } in
  let env = { env with is_native_tactic = FStar.Tactics.Native.is_native_tactic } in
  env.solver.init env;
  env

(***********************************************************************)
(* Checking Prims.fst                                                  *)
(***********************************************************************)
let tc_prims (env: TcEnv.env)
    : (Syntax.modul * int) * TcEnv.env =
  let prims_filename = Options.prims () in
  let prims_mod, env = parse env None prims_filename in
  let (prims_mod, env), elapsed_time =
    record_time (fun () -> Tc.check_module env prims_mod) in
  (prims_mod, elapsed_time), env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
let tc_one_fragment curmod (env:TcEnv.env) (frag, is_interface_dependence) =
  try
    match Parser.Driver.parse_fragment frag with
    | Parser.Driver.Empty ->
      Some (curmod, env)

    | Parser.Driver.Modul ast_modul ->
        (* It may seem surprising that this function, whose name indicates that
        it type-checks a fragment, can actually parse an entire module.
        Actually, this is an abuse, and just means that we're type-checking the
        first chunk. *)
      let ast_modul, env = with_tcenv env <| FStar.ToSyntax.Interleave.interleave_module ast_modul false in
      let modul, env = with_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul in
      let env =
        if is_interface_dependence then
            {env with dsenv=FStar.ToSyntax.Env.set_iface env.dsenv false}
        else env in
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
      let modul, _, env = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                          else Tc.tc_partial_modul env modul in
      Some (Some modul, env)

    | Parser.Driver.Decls ast_decls ->
      let env, ast_decls_l =
            BU.fold_map
                (fun env a_decl ->
                    let decls, env =
                        with_tcenv env <|
                        FStar.ToSyntax.Interleave.prefix_with_interface_decls a_decl
                    in
                    env, decls)
                env
                ast_decls in
      let sigelts, env = with_tcenv env <| Desugar.decls_to_sigelts (List.flatten ast_decls_l) in
      match curmod with
        | None -> FStar.Util.print_error "fragment without an enclosing module"; exit 1
        | Some modul ->
            let modul, _, env  = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                                 else Tc.tc_more_partial_modul env modul sigelts in
            Some (Some modul, env)

    with
      | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,r)];
          None
      | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,Range.dummyRange)];
          None
      | e when not ((Options.trace_error())) -> raise e

let load_interface_decls env interface_file_name : FStar.TypeChecker.Env.env =
  try
    let r = FStar.Parser.ParseIt.parse (Inl interface_file_name) in
    match r with
    | Inl (Inl (FStar.Parser.AST.Interface(l, decls, _)), _) ->
      snd (with_tcenv env <| FStar.ToSyntax.Interleave.initialize_interface l decls)
    | Inl _ ->
      raise (FStar.Errors.Err(BU.format1 "Unexpected result from parsing %s; expected a single interface"
                               interface_file_name))
    | Inr (err, rng) ->
      raise (FStar.Errors.Error(err, rng))
  with
      | FStar.Errors.Error(msg, r) when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,r)];
          env
      | FStar.Errors.Err msg when not ((Options.trace_error())) ->
          TypeChecker.Err.add_errors env [(msg,Range.dummyRange)];
          env
      | e when not ((Options.trace_error())) -> raise e

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)
let tc_one_file env pre_fn fn : (Syntax.modul * int) //checked module and its elapsed checking time
                              * TcEnv.env =
  let checked_file_name = FStar.Parser.ParseIt.find_file fn ^ ".checked" in
  let lax_checked_file_name = checked_file_name ^ ".lax" in
  let lax_ok = not (Options.should_verify_file fn) in
  let cache_file_to_write =
      if lax_ok
      then lax_checked_file_name
      else checked_file_name
  in
  let cache_file_to_read () =
      if BU.file_exists checked_file_name then Some checked_file_name
      else if lax_ok && BU.file_exists lax_checked_file_name
           then Some lax_checked_file_name
           else None
  in
  let tc_source_file () =
      let fmod, env = parse env pre_fn fn in
      let check_mod () =
          let (tcmod, env), time =
            FStar.Util.record_time (fun () -> Tc.check_module env fmod) in
          (tcmod, time), env
      in
      let tcmod, env =
        if (Options.should_verify fmod.name.str //if we're verifying this module
            && (FStar.Options.record_hints() //and if we're recording or using hints
                || FStar.Options.use_hints()))
        then SMT.with_hints_db (FStar.Parser.ParseIt.find_file fn) check_mod
        else check_mod() //don't add a hints file for modules that are not actually verified
      in
      if Options.cache_checked_modules ()
      then begin
        let tcmod, _ = tcmod in
        let mii = FStar.ToSyntax.Env.inclusion_info env.dsenv tcmod.name in
        BU.save_value_to_file cache_file_to_write (BU.digest_of_file fn, tcmod, mii)
      end;
      tcmod, env
  in
  if Options.cache_checked_modules ()
  then match cache_file_to_read () with
       | None -> tc_source_file ()
       | Some cache_file ->
         match BU.load_value_from_file cache_file with
         | None -> failwith ("Corrupt file: " ^ cache_file)
         | Some (digest, tcmod, mii) ->
            if digest = BU.digest_of_file fn
            then let _, env = with_tcenv env <| FStar.ToSyntax.ToSyntax.add_modul_to_env tcmod mii in
                 let env = FStar.TypeChecker.Tc.load_checked_module env tcmod in
                 (tcmod, 0), env
            else failwith (BU.format1 "The file %s is stale; delete it" cache_file)
  else tc_source_file ()

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  List.mem (FStar.Util.get_file_extension intf) ["fsti"; "fsi"] &&
  List.mem (FStar.Util.get_file_extension impl) ["fst"; "fs"]

let pop_context env msg =
    DsEnv.pop () |> ignore;
    TcEnv.pop env msg |> ignore;
    env.solver.refresh()

let push_context env msg =
    let dsenv = DsEnv.push env.dsenv in
    let env = TcEnv.push env msg in
    {env with dsenv=dsenv}

let tc_one_file_from_remaining (remaining:list<string>) (env:TcEnv.env) =
  let remaining, (nmods, env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let m, env = tc_one_file env (Some intf) impl in
          remaining, ([m], env)
        | intf_or_impl :: remaining ->
          let m, env = tc_one_file env None intf_or_impl in
          remaining, ([m], env)
        | [] -> [], ([], env)
  in
  remaining, nmods, env

let rec tc_fold_interleave (acc:list<(modul * int)> * TcEnv.env) (remaining:list<string>) =
  match remaining with
    | [] -> acc
    | _  ->
      let mods, env = acc in
      let remaining, nmods, env = tc_one_file_from_remaining remaining env in
      tc_fold_interleave (mods@nmods, env) remaining

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc_no_prims env filenames =
  let all_mods, env = tc_fold_interleave ([], env) filenames in
  if Options.interactive()
  && FStar.Errors.get_err_count () = 0
  then env.solver.refresh()
  else env.solver.finish();
  all_mods, env

let batch_mode_tc filenames =
  let prims_mod, env = tc_prims (init_env ()) in
  if not (Options.explicit_deps ()) && Options.debug_any () then begin
    FStar.Util.print_endline "Auto-deps kicked in; here's some info.";
    FStar.Util.print1 "Here's the list of filenames we will process: %s\n"
      (String.concat " " filenames);
    FStar.Util.print1 "Here's the list of modules we will verify: %s\n"
      (String.concat " " (Options.verify_module ()))
  end;
  let all_mods, env = batch_mode_tc_no_prims env filenames in
  prims_mod :: all_mods, env

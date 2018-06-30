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
module DsEnv   = FStar.Syntax.DsEnv
module TcEnv   = FStar.TypeChecker.Env
module Syntax  = FStar.Syntax.Syntax
module Util    = FStar.Syntax.Util
module Desugar = FStar.ToSyntax.ToSyntax
module SMT     = FStar.SMTEncoding.Solver
module Const   = FStar.Parser.Const
module Pars    = FStar.Parser.ParseIt
module Tc      = FStar.TypeChecker.Tc
module TcTerm  = FStar.TypeChecker.TcTerm
module BU      = FStar.Util
module Dep     = FStar.Parser.Dep
module NBE     = FStar.TypeChecker.NBE

(* we write this version number to the cache files, and detect when loading the cache that the version number is same *)
let cache_version_number = 4

let module_or_interface_name m = m.is_interface, m.name

let with_tcenv (env:TcEnv.env) (f:DsEnv.withenv<'a>) =
    let a, dsenv = f env.dsenv in
    a, ({ env with dsenv=dsenv })

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
            Errors.raise_err (Errors.Fatal_PreModuleMismatch, "mismatch between pre-module and module\n")
  in
  with_tcenv env <| Desugar.ast_modul_to_modul ast

(***********************************************************************)
(* Initialize a clean environment                                      *)
(***********************************************************************)
let init_env deps : TcEnv.env =
  let solver =
    if Options.lax()
    then SMT.dummy
    else {SMT.solver with preprocess=FStar.Tactics.Interpreter.preprocess} in
  let env =
      TcEnv.initial_env
        deps
        TcTerm.tc_term
        TcTerm.type_of_tot_term
        TcTerm.universe_of
        TcTerm.check_type_of_well_typed_term
        solver
        Const.prims_lid
        (NBE.normalize'' 
          (FStar.Tactics.Interpreter.primitive_steps () @ 
           FStar.Reflection.Interpreter.reflection_primops))
  in
  (* Set up some tactics callbacks *)
  let env = { env with synth_hook = FStar.Tactics.Interpreter.synthesize } in
  let env = { env with splice = FStar.Tactics.Interpreter.splice} in
  let env = { env with is_native_tactic = FStar.Tactics.Native.is_native_tactic } in
  env.solver.init env;
  env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
let tc_one_fragment curmod (env:TcEnv.env) frag =
  let acceptable_mod_name modul =
    (* Interface is sent as the first chunk, so we must allow repeating the same module. *)
    Parser.Dep.lowercase_module_name (List.hd (Options.file_list ())) =
    String.lowercase (string_of_lid modul.name) in

  let range_of_first_mod_decl modul =
    match modul with
    | Parser.AST.Module (_, { Parser.AST.drange = d } :: _)
    | Parser.AST.Interface (_, { Parser.AST.drange = d } :: _, _) -> d
    | _ -> Range.dummyRange in

  match Parser.Driver.parse_fragment frag with
  | Parser.Driver.Empty
  | Parser.Driver.Decls [] ->
    (curmod, env)

  | Parser.Driver.Modul ast_modul ->
    (* It may seem surprising that this function, whose name indicates that
       it type-checks a fragment, can actually parse an entire module.
       Actually, this is an abuse, and just means that we're type-checking the
       first chunk. *)
    let ast_modul, env =
      with_tcenv env <| FStar.ToSyntax.Interleave.interleave_module ast_modul false in
    let modul, env =
      with_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul in
    if not (acceptable_mod_name modul) then
    begin
       let msg : string =
           BU.format1 "Interactive mode only supports a single module at the top-level. Expected module %s"
                       (Parser.Dep.module_name_of_file (List.hd (Options.file_list ())))
       in
       Errors.raise_error (Errors.Fatal_NonSingletonTopLevelModule, msg)
                             (range_of_first_mod_decl ast_modul)
    end;
    let modul, _, env = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                        else Tc.tc_partial_modul env modul in
    (Some modul, env)
  | Parser.Driver.Decls ast_decls ->
    match curmod with
    | None ->
      let { Parser.AST.drange = rng } = List.hd ast_decls in
      Errors.raise_error (Errors.Fatal_ModuleFirstStatement, "First statement must be a module declaration") rng
    | Some modul ->
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
      let modul, _, env  = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                           else Tc.tc_more_partial_modul env modul sigelts in
      (Some modul, env)

let load_interface_decls env interface_file_name : FStar.TypeChecker.Env.env =
  let r = Pars.parse (Pars.Filename interface_file_name) in
  match r with
  | Pars.ASTFragment (Inl (FStar.Parser.AST.Interface(l, decls, _)), _) ->
    snd (with_tcenv env <| FStar.ToSyntax.Interleave.initialize_interface l decls)
  | Pars.ASTFragment _ ->
    Errors.raise_err (FStar.Errors.Fatal_ParseErrors, (BU.format1 "Unexpected result from parsing %s; expected a single interface"
                             interface_file_name))
  | Pars.ParseError (err, msg, rng) ->
    raise (FStar.Errors.Error(err, msg, rng))
  | Pars.Term _ ->
     failwith "Impossible: parsing a Toplevel always results in an ASTFragment"


(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)
let load_module_from_cache
    : env -> string -> option<(Syntax.modul * option<Syntax.modul> * DsEnv.module_inclusion_info)> =
    let some_cache_invalid = BU.mk_ref None in
    let invalidate_cache fn = some_cache_invalid := Some fn in
    let load env source_file cache_file =
        match BU.load_value_from_file cache_file with
        | None ->
            Inl "Corrupt"
        | Some (vnum, digest, tcmod, tcmod_iface_opt, mii) ->
            if vnum <> cache_version_number then Inl "Stale, because inconsistent cache version"
            else
            match FStar.Parser.Dep.hash_dependences env.dep_graph source_file with
            | Some digest' ->
                if digest=digest'
                then Inr (tcmod, tcmod_iface_opt, mii)
                else begin
                if Options.debug_any()
                then begin
                    BU.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
                            (BU.string_of_int (List.length digest'))
                            (FStar.Parser.Dep.print_digest digest')
                            (BU.string_of_int (List.length digest))
                            (FStar.Parser.Dep.print_digest digest);
                    if List.length digest = List.length digest'
                    then List.iter2
                        (fun (x,y) (x', y') ->
                        if x<>x' || y<>y'
                        then BU.print2 "Differ at: Expected %s\n Got %s\n"
                                        (FStar.Parser.Dep.print_digest [(x,y)])
                                        (FStar.Parser.Dep.print_digest [(x',y')]))
                        digest
                        digest'
                end;
                Inl "Stale"
                end
            | _ ->
                Inl "Unable to compute digest of"
    in
    fun env fn ->
        let cache_file = Dep.cache_file_name fn in
        let fail tag should_warn cache_file =
             invalidate_cache();
             if should_warn then
                 FStar.Errors.log_issue
                    (Range.mk_range fn (Range.mk_pos 0 0) (Range.mk_pos 0 0))
                    (Errors.Warning_CachedFile,
                     BU.format3 "%s cache file %s; will recheck %s and all subsequent files" tag cache_file fn);
             None
        in
        match !some_cache_invalid with
        | Some _ -> None
        | _ ->
          if BU.file_exists cache_file then
            match load env fn cache_file with
            | Inl msg -> fail msg true cache_file
            | Inr res -> Some res
          else
            match FStar.Options.find_file (FStar.Util.basename cache_file) with
            | None -> fail "Absent" false cache_file //do not warn if the file was not found
            | Some alt_cache_file ->
              match load env fn alt_cache_file with
              | Inl msg -> fail msg true alt_cache_file
              | Inr res ->
                //found a valid .checked file somewhere else in the include path
                //copy it to the destination, if we are supposed to be verifying this file
                if Options.should_verify_file fn
                then FStar.Util.copy_file alt_cache_file cache_file;
                Some res


let store_module_to_cache env fn (m:modul) (modul_iface_opt:option<modul>) (mii:DsEnv.module_inclusion_info) =
    if Options.cache_checked_modules()
    && not (Options.cache_off())
    then begin
        let cache_file = FStar.Parser.Dep.cache_file_name fn in
        let digest = FStar.Parser.Dep.hash_dependences env.dep_graph fn in
        match digest with
        | Some hashes ->
          //cache_version_number should always be the first field here
          BU.save_value_to_file cache_file (cache_version_number, hashes, m, modul_iface_opt, mii)
        | _ ->
          FStar.Errors.log_issue
            (FStar.Range.mk_range fn (FStar.Range.mk_pos 0 0)
                                     (FStar.Range.mk_pos 0 0))
            (Errors.Warning_FileNotWritten, BU.format1 "%s was not written, since some of its dependences were not also checked"
                        cache_file)
    end

(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)
type delta_env = option<(env -> env)>
let apply_delta_env env (f:delta_env) =
    match f with
    | None -> env
    | Some f -> f env
let extend_delta_env (f:delta_env) (g:env->env) =
    match f with
    | None -> Some g
    | Some f -> Some (fun e -> g (f e))
let tc_one_file env delta pre_fn fn : (Syntax.modul * int) //checked module and its elapsed checking time
                                    * TcEnv.env
                                    * delta_env =
  Syntax.reset_gensym();
  let tc_source_file () =
      let env = apply_delta_env env delta in
      let fmod, env = parse env pre_fn fn in
      let check_mod () =
          let (tcmod, tcmod_iface_opt, env), time =
            FStar.Util.record_time (fun () -> Tc.check_module env fmod (is_some pre_fn)) in
          (tcmod, time), tcmod_iface_opt, env
      in
      let tcmod, tcmod_iface_opt, env =
        if (Options.should_verify fmod.name.str //if we're verifying this module
            && (FStar.Options.record_hints() //and if we're recording or using hints
                || FStar.Options.use_hints()))
        then SMT.with_hints_db (Pars.find_file fn) check_mod
        else check_mod () //don't add a hints file for modules that are not actually verified
      in
      let mii = FStar.Syntax.DsEnv.inclusion_info env.dsenv (fst tcmod).name in
      tcmod, tcmod_iface_opt, mii, env
  in
  if not (Options.cache_off()) then
      match load_module_from_cache env fn with
      | None ->
            let tcmod, tcmod_iface_opt, mii, env = tc_source_file () in
            if FStar.Errors.get_err_count() = 0
            && (Options.lax()  //we'll write out a .checked.lax file
                || Options.should_verify (fst tcmod).name.str) //we'll write out a .checked file
            //but we will not write out a .checked file for an unverified dependence
            //of some file that should be checked
            then store_module_to_cache env fn (fst tcmod) tcmod_iface_opt mii;
            tcmod, env, None
      | Some (tcmod, tcmod_iface_opt, mii) ->
            if Options.dump_module tcmod.name.str
            then BU.print1 "Module after type checking:\n%s\n" (FStar.Syntax.Print.modul_to_string tcmod);
            let tcmod =
            if tcmod.is_interface then tcmod
            else
                let use_interface_from_the_cache = Options.use_extracted_interfaces () && pre_fn = None &&
                                                (not (Options.expose_interfaces ()  && Options.should_verify tcmod.name.str)) in
                if use_interface_from_the_cache then
                if tcmod_iface_opt = None then
                begin
                    FStar.Errors.log_issue (Range.mk_range tcmod.name.str
                                                        (Range.mk_pos 0 0)
                                                        (Range.mk_pos 0 0))
                                        (Errors.Warning_MissingInterfaceOrImplementation,
                                            "use_extracted_interfaces option is set \
                                            but could not find an interface in the cache for: "
                                            ^ tcmod.name.str);
                    tcmod
                end
                else tcmod_iface_opt |> must
                else tcmod
            in
            let delta_env env =
                let _, env =
                with_tcenv env <|
                FStar.ToSyntax.ToSyntax.add_modul_to_env tcmod mii (FStar.TypeChecker.Normalize.erase_universes env)
                in
                FStar.TypeChecker.Tc.load_checked_module env tcmod
            in
            (tcmod,0), env, extend_delta_env delta delta_env
  else let tcmod, tcmod_iface_opt, _, env = tc_source_file () in
       let tcmod = if is_some tcmod_iface_opt then (tcmod_iface_opt |> must, snd tcmod) else tcmod in  //AR: TODO: does it matter what we return here?
       tcmod, env, None


(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  List.mem (FStar.Util.get_file_extension intf) ["fsti"; "fsi"] &&
  List.mem (FStar.Util.get_file_extension impl) ["fst"; "fs"]

let tc_one_file_from_remaining (remaining:list<string>) (env:TcEnv.env) (delta_env:delta_env) =
  let remaining, (nmods, env, delta_env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let m, env, delta_env = tc_one_file env delta_env (Some intf) impl in
          remaining, ([m], env, delta_env)
        | intf_or_impl :: remaining ->
          let m, env, delta_env = tc_one_file env delta_env None intf_or_impl in
          remaining, ([m], env, delta_env)
        | [] -> [], ([], env, delta_env)
  in
  remaining, nmods, env, delta_env

let rec tc_fold_interleave (acc:list<(modul * int)> * TcEnv.env * delta_env) (remaining:list<string>) =
  match remaining with
    | [] -> acc
    | _  ->
      let mods, env, delta_env = acc in
      let remaining, nmods, env, delta_env = tc_one_file_from_remaining remaining env delta_env in
      tc_fold_interleave (mods@nmods, env, delta_env) remaining

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc filenames dep_graph =
  if Options.debug_any () then begin
    FStar.Util.print_endline "Auto-deps kicked in; here's some info.";
    FStar.Util.print1 "Here's the list of filenames we will process: %s\n"
      (String.concat " " filenames);
    FStar.Util.print1 "Here's the list of modules we will verify: %s\n"
      (String.concat " " (filenames |> List.filter Options.should_verify_file))
  end;
  let env = init_env dep_graph in
  let all_mods, env, delta = tc_fold_interleave ([], env, None) filenames in
  let solver_refresh env =
      begin
      if Options.interactive()
      && FStar.Errors.get_err_count () = 0
      then env.solver.refresh()
      else env.solver.finish()
      end;
      env
  in
  all_mods, env, extend_delta_env delta solver_refresh

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
open FStar.Dependencies
open FStar.Extraction.ML.UEnv
open FStar.TypeChecker.Env
open FStar.Syntax.DsEnv
open FStar.TypeChecker
open FStar.CheckedFiles
open FStar.Profiling

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
module Ch      = FStar.CheckedFiles
module P       = FStar.Profiling
let module_or_interface_name m = m.is_interface, m.name

type uenv = FStar.Extraction.ML.UEnv.uenv

let with_dsenv_of_tcenv (tcenv:TcEnv.env) (f:DsEnv.withenv<'a>) : 'a * TcEnv.env =
    let a, dsenv = f tcenv.dsenv in
    a, ({tcenv with dsenv = dsenv})

let with_tcenv_of_env (e:uenv) (f:TcEnv.env -> 'a * TcEnv.env) : 'a * uenv =
     let a, t' = f e.env_tcenv in
     a, ({e with env_tcenv=t'})

let with_dsenv_of_env (e:uenv) (f:DsEnv.withenv<'a>) : 'a * uenv =
     let a, tcenv = with_dsenv_of_tcenv e.env_tcenv f in
     a, ({e with env_tcenv=tcenv})

let push_env (env:uenv) =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStar.TypeChecker.Env.push env.env_tcenv "top-level: push_env"))

let pop_env (env:uenv) =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStar.TypeChecker.Env.pop tcenv "top-level: pop_env"))

let with_env env (f:uenv -> 'a) : 'a =
    let env = push_env env in
    let res = f env in
    let _ = pop_env env in
    res

let env_of_tcenv (env:TcEnv.env) =
    FStar.Extraction.ML.UEnv.mkContext env

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:uenv) (pre_fn: option<string>) (fn:string)
  : Syntax.modul
  * uenv =
  let ast, _ = Parser.Driver.parse_file fn in
  let ast, env = match pre_fn with
    | None ->
        ast, env
    | Some pre_fn ->
        let pre_ast, _ = Parser.Driver.parse_file pre_fn in
        match pre_ast, ast with
        | Parser.AST.Interface (lid1, decls1, _), Parser.AST.Module (lid2, decls2)
          when Ident.lid_equals lid1 lid2 ->
          let _, env =
            with_dsenv_of_env env (FStar.ToSyntax.Interleave.initialize_interface lid1 decls1)
          in
          with_dsenv_of_env env (FStar.ToSyntax.Interleave.interleave_module ast true)
        | _ ->
            Errors.raise_err (Errors.Fatal_PreModuleMismatch, "mismatch between pre-module and module\n")
  in
  with_dsenv_of_env env (Desugar.ast_modul_to_modul ast)

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
        (NBE.normalize
          (FStar.Tactics.Interpreter.primitive_steps ()))
  in
  (* Set up some tactics callbacks *)
  let env = { env with synth_hook       = FStar.Tactics.Interpreter.synthesize } in
  let env = { env with splice           = FStar.Tactics.Interpreter.splice} in
  let env = { env with postprocess      = FStar.Tactics.Interpreter.postprocess} in
  let env = { env with is_native_tactic = FStar.Tactics.Native.is_native_tactic } in
  env.solver.init env;
  env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
let tc_one_fragment curmod (env:TcEnv.env_t) frag =
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
      with_dsenv_of_tcenv env <| FStar.ToSyntax.Interleave.interleave_module ast_modul false in
    let modul, env =
      with_dsenv_of_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul in
    if not (acceptable_mod_name modul) then
    begin
       let msg : string =
           BU.format1 "Interactive mode only supports a single module at the top-level. Expected module %s"
                       (Parser.Dep.module_name_of_file (List.hd (Options.file_list ())))
       in
       Errors.raise_error (Errors.Fatal_NonSingletonTopLevelModule, msg)
                             (range_of_first_mod_decl ast_modul)
    end;
    let (modul, _), env =
        if DsEnv.syntax_only env.dsenv then (modul, []), env
        else let m, i, e = Tc.tc_partial_modul env modul in
                (m, i), e
    in
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
                    with_dsenv_of_tcenv env <|
                    FStar.ToSyntax.Interleave.prefix_with_interface_decls a_decl
                in
                env, decls)
            env
            ast_decls in
      let sigelts, env = with_dsenv_of_tcenv env <| Desugar.decls_to_sigelts (List.flatten ast_decls_l) in
      let modul, _, env  = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                        else Tc.tc_more_partial_modul env modul sigelts in
      (Some modul, env)

let load_interface_decls env interface_file_name : TcEnv.env_t =
  let r = Pars.parse (Pars.Filename interface_file_name) in
  match r with
  | Pars.ASTFragment (Inl (FStar.Parser.AST.Interface(l, decls, _)), _) ->
    snd (with_dsenv_of_tcenv env <| FStar.ToSyntax.Interleave.initialize_interface l decls)
  | Pars.ASTFragment _ ->
    Errors.raise_err (FStar.Errors.Fatal_ParseErrors, (BU.format1 "Unexpected result from parsing %s; expected a single interface"
                             interface_file_name))
  | Pars.ParseError (err, msg, rng) ->
    raise (FStar.Errors.Error(err, msg, rng))
  | Pars.Term _ ->
     failwith "Impossible: parsing a Toplevel always results in an ASTFragment"


(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)

(* Extraction to OCaml, F# or Kremlin *)
let emit (mllibs:list<FStar.Extraction.ML.Syntax.mllib>) =
  let opt = Options.codegen () in
  if opt <> None then
    let ext = match opt with
      | Some Options.FSharp -> ".fs"
      | Some Options.OCaml
      | Some Options.Plugin -> ".ml"
      | Some Options.Kremlin -> ".krml"
      | _ -> failwith "Unrecognized option"
    in
    match opt with
    | Some Options.FSharp | Some Options.OCaml | Some Options.Plugin ->
        (* When bootstrapped in F#, this will use the old printer in
           FStar.Extraction.ML.Code for both OCaml and F# extraction.
           When bootstarpped in OCaml, this will use the old printer
           for F# extraction and the new printer for OCaml extraction. *)
        let outdir = Options.output_dir() in
        List.iter (FStar.Extraction.ML.PrintML.print outdir ext) mllibs
    | Some Options.Kremlin ->
        let programs = List.collect Extraction.Kremlin.translate mllibs in
        let bin: Extraction.Kremlin.binary_format = Extraction.Kremlin.current_version, programs in
        begin match programs with
        | [ name, _ ] ->
            save_value_to_file (Options.prepend_output_dir (name ^ ext)) bin
        | _ ->
            save_value_to_file (Options.prepend_output_dir "out.krml") bin
        end
   | _ -> failwith "Unrecognized option"

let tc_one_file
        (env:uenv)
        (pre_fn:option<string>) //interface file name
        (fn:string) //file name
        (parsing_data:FStar.Parser.Dep.parsing_data)  //passed by the caller, ONLY for caching purposes at this point
    : tc_result
    * option<FStar.Extraction.ML.Syntax.mllib>
    * uenv =
  Ident.reset_gensym();

  (*
   * AR: smt encode_modul functions are now here instead of in Tc.fs
   *     this is common smt postprocessing for fresh module and module read from cache
   *)
  let maybe_restore_opts () : unit =
    if not (Options.interactive ()) then
      Options.restore_cmd_line_options true |> ignore
  in
  let post_smt_encoding (_:unit) :unit =
    FStar.SMTEncoding.Z3.refresh ()
  in
  let maybe_extract_mldefs tcmod env =
      if Options.codegen() = None
      || not (Options.should_extract tcmod.name.str)
      then None, 0
      else FStar.Util.record_time (fun () ->
            let _, defs = FStar.Extraction.ML.Modul.extract env tcmod in
            defs)
  in
  let maybe_extract_ml_iface tcmod env =
       if Options.codegen() = None
       then env, 0
       else let (env, _extracted_iface), iface_extract_time =
              FStar.Util.record_time (fun () ->
                  FStar.Extraction.ML.Modul.extract_iface env tcmod)
            in
            env, iface_extract_time
  in
  let tc_source_file () =
      let fmod, env = parse env pre_fn fn in
      let mii = FStar.Syntax.DsEnv.inclusion_info env.env_tcenv.dsenv fmod.name in
      let check_mod () =
          let _ = if (Options.profile_module fmod.name.str) then P.init_profiler () else P.disable_profiler () in
          let check env =
              with_tcenv_of_env env (fun tcenv ->
                 let _ = match tcenv.gamma with
                         | [] -> ()
                         | _ -> failwith "Impossible: gamma contains leaked names"
                 in
                 let modul, env = Tc.check_module tcenv fmod (is_some pre_fn) in
                 //AR: encode the module to to smt
                 maybe_restore_opts ();
                 let smt_decls =
                   if (not (Options.lax()))
                   then let smt_decls = FStar.SMTEncoding.Encode.encode_modul env modul in
                        post_smt_encoding ();
                        smt_decls
                   else [], []
                 in
                 ((modul, smt_decls), env))
            in
          
          let ((tcmod, smt_decls), env), tc_time =
            if (Options.profile_at_level Options.Module) then
              P.profile (fun() -> check env) 
                     fmod.name.str "module" 
                     (Options.profile_at_level Options.Module)
            else 
              FStar.Util.record_time (fun () -> check env) 
          in
          
          let extracted_defs, extract_time = with_env env (maybe_extract_mldefs tcmod) in
          let env, iface_extraction_time = with_env env (maybe_extract_ml_iface tcmod) in
          {
            checked_module=tcmod;
            tc_time=tc_time;
            smt_decls=smt_decls;

            extraction_time = extract_time + iface_extraction_time;
            mii = mii
          },
          extracted_defs,
          env
      in
      if (Options.should_verify fmod.name.str //if we're verifying this module
            && (FStar.Options.record_hints() //and if we're recording or using hints
                || FStar.Options.use_hints()))
      then SMT.with_hints_db (Pars.find_file fn) check_mod
      else check_mod () //don't add a hints file for modules that are not actually verified
  in
  if not (Options.cache_off()) then
      match Ch.load_module_from_cache env fn with
      | None ->
        if Options.should_be_already_cached (FStar.Parser.Dep.module_name_of_file fn)
        then FStar.Errors.raise_err
                (FStar.Errors.Error_AlreadyCachedAssertionFailure,
                 BU.format1 "Expected %s to already be checked" fn);

        if (Option.isSome (Options.codegen())
        && Options.cmi())
        then FStar.Errors.raise_err
                (FStar.Errors.Error_AlreadyCachedAssertionFailure,
                 BU.format1 "Cross-module inlining expects all modules to be checked first; %s was not checked"
                            fn);


        let tc_result, mllib, env = tc_source_file () in
        if FStar.Errors.get_err_count() = 0
        && (Options.lax()  //we'll write out a .checked.lax file
            || Options.should_verify tc_result.checked_module.name.str) //we'll write out a .checked file
        //but we will not write out a .checked file for an unverified dependence
        //of some file that should be checked
        then Ch.store_module_to_cache env fn parsing_data tc_result;
        tc_result, mllib, env

      | Some tc_result ->
        let tcmod = tc_result.checked_module in
        let smt_decls = tc_result.smt_decls in
        if Options.dump_module tcmod.name.str
        then BU.print1 "Module after type checking:\n%s\n" (FStar.Syntax.Print.modul_to_string tcmod);

        let extend_tcenv tcmod tcenv =
            let _, tcenv =
                with_dsenv_of_tcenv tcenv <|
                    FStar.ToSyntax.ToSyntax.add_modul_to_env
                        tcmod
                        tc_result.mii
                        (FStar.TypeChecker.Normalize.erase_universes tcenv)
            in
            let env = FStar.TypeChecker.Tc.load_checked_module tcenv tcmod in
            maybe_restore_opts ();
            //AR: encode smt module and do post processing
            if (not (Options.lax())) then begin
              FStar.SMTEncoding.Encode.encode_modul_from_cache env tcmod.name smt_decls;
              post_smt_encoding ()
            end;
            (), env
        in

        let env =
          Options.profile
            (fun () -> with_tcenv_of_env env (extend_tcenv tcmod) |> snd)
            (fun _ -> BU.format1 "Extending environment with module %s"
                                 tcmod.name.str) in


        (* If we have to extract this module, then do it first *)
        let mllib =
            if Options.codegen()<>None
            && Options.should_extract tcmod.name.str
            && (not tcmod.is_interface || Options.codegen()=Some Options.Kremlin)
            then with_env env (fun env ->
                   let extracted_defs, _extraction_time = maybe_extract_mldefs tcmod env in
                   extracted_defs)
            else None
        in

        let env, _time = with_env env (maybe_extract_ml_iface tcmod) in

        tc_result,
        mllib,
        env

  else let tc_result, mllib, env = tc_source_file () in
       tc_result, mllib, env

let tc_one_file_for_ide
        (env:TcEnv.env_t)
        (pre_fn:option<string>) //interface file name
        (fn:string) //file name
        (parsing_data:FStar.Parser.Dep.parsing_data)  //threaded along, ONLY for caching purposes at this point
    : tc_result
    * TcEnv.env_t
    =
    let env = env_of_tcenv env in
    let tc_result, _, env = tc_one_file env pre_fn fn parsing_data in
    tc_result, env.env_tcenv

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  List.mem (FStar.Util.get_file_extension intf) ["fsti"; "fsi"] &&
  List.mem (FStar.Util.get_file_extension impl) ["fst"; "fs"]

let tc_one_file_from_remaining (remaining:list<string>) (env:uenv)
                               (deps:FStar.Parser.Dep.deps)  //used to query parsing data
  =
  let remaining, (nmods, mllib, env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let m, mllib, env = tc_one_file env (Some intf) impl
                                          (impl |> FStar.Parser.Dep.parsing_data_of deps) in
          remaining, ([m], mllib, env)
        | intf_or_impl :: remaining ->
          let m, mllib, env = tc_one_file env None intf_or_impl
                                          (intf_or_impl |> FStar.Parser.Dep.parsing_data_of deps) in
          remaining, ([m], mllib, env)
        | [] -> [], ([], None, env)
  in
  remaining, nmods, mllib, env

let rec tc_fold_interleave (deps:FStar.Parser.Dep.deps)  //used to query parsing data
                           (acc:list<tc_result> * list<FStar.Extraction.ML.Syntax.mllib> * uenv)
                           (remaining:list<string>) =
  let as_list = function None -> [] | Some l -> [l] in
  match remaining with
    | [] -> acc
    | _  ->
      let mods, mllibs, env = acc in
      let remaining, nmods, mllib, env = tc_one_file_from_remaining remaining env deps in
      tc_fold_interleave deps (mods@nmods, mllibs@as_list mllib, env) remaining

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
  let env = FStar.Extraction.ML.UEnv.mkContext (init_env dep_graph) in
  let all_mods, mllibs, env = tc_fold_interleave dep_graph ([], [], env) filenames in
  emit mllibs;
  let solver_refresh env =
      snd <|
      with_tcenv_of_env env (fun tcenv ->
          if Options.interactive()
          && FStar.Errors.get_err_count () = 0
          then tcenv.solver.refresh()
          else tcenv.solver.finish();
          (), tcenv)
  in
  all_mods, env, solver_refresh

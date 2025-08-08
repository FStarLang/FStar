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

//Top-level invocations into the universal type-checker FStarC.TypeChecker
module FStarC.Universal
open FStarC.Effect
open FStarC.List
open FStarC
open FStarC.Errors
open FStarC.Util
open FStarC.Getopt
open FStarC.Ident
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Common
open FStarC.Dependencies
open FStarC.Extraction.ML.UEnv
open FStarC.TypeChecker.Env
open FStarC.Syntax.DsEnv
open FStarC.TypeChecker
open FStarC.CheckedFiles

open FStarC.Class.Show

(* Module abbreviations for the universal type-checker  *)
module DsEnv    = FStarC.Syntax.DsEnv
module TcEnv    = FStarC.TypeChecker.Env
module Syntax   = FStarC.Syntax.Syntax
module Util     = FStarC.Syntax.Util
module Desugar  = FStarC.ToSyntax.ToSyntax
module SMT      = FStarC.SMTEncoding.Solver
module Const    = FStarC.Parser.Const
module Pars     = FStarC.Parser.ParseIt
module Tc       = FStarC.TypeChecker.Tc
module TcTerm   = FStarC.TypeChecker.TcTerm
module BU       = FStarC.Util
module Dep      = FStarC.Parser.Dep
module NBE      = FStarC.TypeChecker.NBE
module Ch       = FStarC.CheckedFiles
module MLSyntax = FStarC.Extraction.ML.Syntax

let module_or_interface_name m = m.is_interface, m.name

let with_dsenv_of_tcenv (tcenv:TcEnv.env) (f:DsEnv.withenv 'a) : 'a & TcEnv.env =
    let a, dsenv = f tcenv.dsenv in
    a, ({tcenv with dsenv = dsenv})

let with_tcenv_of_env (e:uenv) (f:TcEnv.env -> 'a & TcEnv.env) : 'a & uenv =
     let a, t' = f (tcenv_of_uenv e) in
     a, (set_tcenv e t')

let with_dsenv_of_env (e:uenv) (f:DsEnv.withenv 'a) : 'a & uenv =
     let a, tcenv = with_dsenv_of_tcenv (tcenv_of_uenv e) f in
     a, (set_tcenv e tcenv)

let push_env (env:uenv) =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStarC.TypeChecker.Env.push (tcenv_of_uenv env) "top-level: push_env"))

let pop_env (env:uenv) =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStarC.TypeChecker.Env.pop tcenv "top-level: pop_env"))

let with_env env (f:uenv -> 'a) : 'a =
    let env = push_env env in
    let res = f env in
    let _ = pop_env env in
    res

let env_of_tcenv (env:TcEnv.env) =
    FStarC.Extraction.ML.UEnv.new_uenv env

(***********************************************************************)
(* Parse and desugar a file                                            *)
(***********************************************************************)
let parse (env:uenv) (pre_fn: option string) (fn:string)
  : Syntax.modul
  & uenv =
  let ast, _ = Parser.Driver.parse_file fn in
  let ast, env = match pre_fn with
    | None ->
        ast, env
    | Some pre_fn ->
        let pre_ast, _ = Parser.Driver.parse_file pre_fn in
        match pre_ast, ast with
        | Parser.AST.Interface {mname=lid1; decls=decls1}, Parser.AST.Module {mname=lid2; decls=decls2}
          when Ident.lid_equals lid1 lid2 ->
          let _, env =
            with_dsenv_of_env env (FStarC.ToSyntax.Interleave.initialize_interface lid1 decls1)
          in
          with_dsenv_of_env env (FStarC.ToSyntax.Interleave.interleave_module ast true)

        | Parser.AST.Interface {mname=lid1}, Parser.AST.Interface {mname=lid2} ->
          (* Names do not match *)
          Errors.raise_error lid1
            Errors.Fatal_PreModuleMismatch
            "Module name in implementation does not match that of interface."

        | _ ->
          Errors.raise_error0
            Errors.Fatal_PreModuleMismatch
            "Module name in implementation does not match that of interface."
  in
  with_dsenv_of_env env (Desugar.ast_modul_to_modul ast)

(***********************************************************************)
(* Initialize a clean environment                                      *)
(***********************************************************************)
let core_check : TcEnv.core_check_t =
  fun env tm t must_tot ->
    let open FStarC.TypeChecker.Core in
    if not (Options.compat_pre_core_should_check ())
    then Inl None
    else match check_term env tm t must_tot with
         | Inl None -> Inl None
         | Inl (Some g) ->
           if Options.compat_pre_core_set ()
           then Inl None
           else Inl (Some g)
         | Inr err ->
           Inr (fun b -> if b then print_error_short err else print_error err)
    
let init_env deps : TcEnv.env =
  let solver =
    if Options.lax()
    then SMT.dummy
    else {SMT.solver with
      preprocess=FStarC.Tactics.Hooks.preprocess;
      spinoff_strictly_positive_goals=Some FStarC.Tactics.Hooks.spinoff_strictly_positive_goals;
      handle_smt_goal=FStarC.Tactics.Hooks.handle_smt_goal
    } in
  let env =
      TcEnv.initial_env
        deps
        TcTerm.tc_term
        TcTerm.typeof_tot_or_gtot_term
        TcTerm.typeof_tot_or_gtot_term_fastpath
        TcTerm.universe_of
        Rel.teq_nosmt_force
        Rel.subtype_nosmt_force
        solver
        Const.prims_lid
        (NBE.normalize
          (FStarC.Tactics.Interpreter.primitive_steps ()))
        core_check
  in
  (* Set up some tactics callbacks *)
  let env = { env with synth_hook       = FStarC.Tactics.Hooks.synthesize } in
  let env = { env with try_solve_implicits_hook = FStarC.Tactics.Hooks.solve_implicits } in
  let env = { env with splice           = FStarC.Tactics.Hooks.splice} in
  let env = { env with mpreprocess      = FStarC.Tactics.Hooks.mpreprocess} in
  let env = { env with postprocess      = FStarC.Tactics.Hooks.postprocess} in
  env.solver.init env;
  env

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
let tc_one_fragment curmod (env:TcEnv.env_t) frag =
    let open FStarC.Parser.AST in
  // We use file_of_range instead of `Options.file_list ()` because no file
  // is passed as a command-line argument in LSP mode.
  let fname env = if Options.lsp_server () then Range.file_of_range (TcEnv.get_range env)
                  else List.hd (Options.file_list ()) in
  let acceptable_mod_name modul =
    (* Interface is sent as the first chunk, so we must allow repeating the same module. *)
    Parser.Dep.lowercase_module_name (fname env) =
    String.lowercase (string_of_lid modul.name) in

  let range_of_first_mod_decl modul =
    match modul with
    | Parser.AST.Module {decls = d :: _} -> d.drange
    | Parser.AST.Interface {decls = d :: _} -> d.drange
    | _ -> Range.dummyRange in

  let filter_lang_decls (d:FStarC.Parser.AST.decl) =
    match d.d with
    | UseLangDecls _ -> true
    | _ -> false
  in
  let use_lang_decl (ds:lang_decls_t) =
    List.tryFind (fun d -> UseLangDecls? d.d) ds
  in
  let check_module_name_declaration ast_modul = 
      (* It may seem surprising that this function, whose name indicates that
         it type-checks a fragment, can actually parse an entire module.
         Actually, this is an abuse, and just means that we're type-checking the
         first chunk. *)
      let ast_modul, env =
        with_dsenv_of_tcenv env <| FStarC.ToSyntax.Interleave.interleave_module ast_modul false in
      let modul, env =
        with_dsenv_of_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul in
      if not (acceptable_mod_name modul) then
      begin
        let msg : string =
            Format.fmt1 "Interactive mode only supports a single module at the top-level. Expected module %s"
                                    (Parser.Dep.module_name_of_file (fname env))
        in
        Errors.raise_error (range_of_first_mod_decl ast_modul) Errors.Fatal_NonSingletonTopLevelModule msg
      end;
      let modul, env =
          if DsEnv.syntax_only env.dsenv then modul, env
          else Tc.tc_partial_modul env modul
      in
      let lang_decls =
        let open FStarC.Parser.AST in
        let decls =
          match ast_modul with
          | Module {decls}
          | Interface {decls} -> decls
        in
        List.filter filter_lang_decls decls
      in
      Some modul, env, lang_decls
  in
  
  let check_decls ast_decls =
    match curmod with
    | None ->
      let { Parser.AST.drange = rng } = List.hd ast_decls in
      Errors.raise_error rng Errors.Fatal_ModuleFirstStatement "First statement must be a module declaration"
    | Some modul ->
      let env, ast_decls_l =
        BU.fold_map
            (fun env a_decl ->
                let decls, env =
                    with_dsenv_of_tcenv env <|
                    FStarC.ToSyntax.Interleave.prefix_with_interface_decls modul.name a_decl
                in
                env, decls)
            env
            ast_decls in
      let sigelts, env = with_dsenv_of_tcenv env <| Desugar.decls_to_sigelts (List.flatten ast_decls_l) in
      let modul, _, env  = if DsEnv.syntax_only env.dsenv then (modul, [], env)
                        else Tc.tc_more_partial_modul env modul sigelts in
      Some modul, env, List.filter filter_lang_decls ast_decls
  in
  match frag with
  | Inr d -> (
    //We already have a parsed decl, usually from FStarC.Interactive.Incremental
    match d.d with
    | FStarC.Parser.AST.TopLevelModule lid ->
      let no_prelude =
        Options.no_prelude () || (* only affects current module *)
        d.attrs |> List.existsb (function t ->
          match t.tm with
          | Const (FStarC.Const.Const_string ("no_prelude", _)) -> true
          | _ -> false)
      in
      let modul = Parser.AST.Module { mname = lid; decls = [d]; no_prelude } in
      check_module_name_declaration modul
    | _ -> 
      check_decls [d]
  )

  | Inl (frag, lang_decls) -> (
    let parse_frag frag =
      match use_lang_decl lang_decls with
      | None -> Parser.Driver.parse_fragment None frag
      | Some {d=UseLangDecls lang} ->
        Parser.Driver.parse_fragment (Some lang) frag
    in
    match parse_frag frag with
    | Parser.Driver.Empty
    | Parser.Driver.Decls [] ->
      curmod, env, []

    | Parser.Driver.Modul ast_modul ->
      check_module_name_declaration ast_modul

    | Parser.Driver.Decls ast_decls ->
      check_decls ast_decls
  )
    
let load_interface_decls env interface_file_name : TcEnv.env_t =
  let r = Pars.parse None (Pars.Filename interface_file_name) in
  match r with
  | Pars.ASTFragment (Inl (FStarC.Parser.AST.Interface {mname=l; decls}), _) ->
    snd (with_dsenv_of_tcenv env <| FStarC.ToSyntax.Interleave.initialize_interface l decls)
  | Pars.ASTFragment _ ->
    Errors.raise_error0 FStarC.Errors.Fatal_ParseErrors
      (Format.fmt1 "Unexpected result from parsing %s; expected a single interface" interface_file_name)
  | Pars.ParseError (err, msg, rng) ->
    raise (FStarC.Errors.Error(err, msg, rng, []))
  | Pars.Term _ ->
     failwith "Impossible: parsing a Toplevel always results in an ASTFragment"


(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)

(* Extraction to OCaml, F# or Krml *)
let emit dep_graph (mllib : list (uenv & MLSyntax.mlmodule)) =
  let opt = Options.codegen () in
  let fail #a () : a = failwith ("Unrecognized extraction backend: " ^ show opt) in
  if opt <> None then
    let ext = match opt with
      | Some Options.FSharp -> ".fs"
      | Some Options.OCaml
      | Some Options.Plugin
      | Some Options.PluginNoLib -> ".ml"
      | Some Options.Krml -> ".krml"
      | Some Options.Extension -> ".ast"
      | _ -> fail ()
    in

    (* The output filename can be overriden with -o, but see the length checks below
    so we only allow this if a single file is going to be extracted, otherwise we would
    clobber them. *)
    let ofile (basename : string) =
      match Options.output_to () with
      | Some fn -> fn
      | None -> Find.prepend_output_dir basename
    in

    match opt with
    | Some Options.FSharp | Some Options.OCaml | Some Options.Plugin | Some Options.PluginNoLib ->
      let printer =
        if opt = Some Options.FSharp
        then FStarC.Extraction.ML.PrintFS.print_fs
        else FStarC.Extraction.ML.PrintML.print_ml
      in

      if Some? (Options.output_to ()) && List.length mllib > 1 then
        raise_error0 Errors.Fatal_OptionsNotCompatible [
          text "Cannot provide -o and extract multiple modules";
          text "Please use -o with a single module, or specify an output directory with --odir";
        ];

      mllib |> List.iter (fun (_, mlmodule) ->
        let p, _ = mlmodule in
        let filename =
          let basename = FStarC.Extraction.ML.Util.flatten_mlpath p ^ ext in
          ofile basename
        in
        let ml = printer mlmodule in
        write_file filename ml)

    | Some Options.Extension ->
      //
      // In the Extension mode, we dump (list mname & bindings_of_uenv & ml decls)
      //   in the binary format to a file
      // The first component is the list of dependencies
      //
      if Some? (Options.output_to ()) && List.length mllib > 1 then
        raise_error0 Errors.Fatal_OptionsNotCompatible [
          text "Cannot provide -o and extract multiple modules";
          text "Please use -o with a single module, or specify an output directory with --odir";
        ];

      mllib |>
      List.iter (fun (env, m) ->
        let mname, modul = m in
        let filename =
          let basename = FStarC.Extraction.ML.Util.flatten_mlpath mname ^ ext in
          ofile basename
        in
        match modul with
        | Some (_, decls) ->
          let bindings = FStarC.Extraction.ML.UEnv.bindings_of_uenv env in
          let deps : list string = Dep.deps_of_modul dep_graph (MLSyntax.string_of_mlpath mname) in
          save_value_to_file filename (deps, bindings, decls)
        | None ->
          failwith "Unexpected ml modul in Extension extraction mode"
      )

    | Some Options.Krml ->
      let programs =
        mllib |> List.collect (fun (ue, m) -> Extraction.Krml.translate ue [m])
      in
      let bin: Extraction.Krml.binary_format = Extraction.Krml.current_version, programs in
      let oname : string =
        (* note: -o implies --krmloutput *)
        match Options.krmloutput () with
        | Some fname -> fname (* NB: no prepending odir nor adding extension, user chose a explicit path *)
        | _ ->
          match programs with
          | [ name, _ ] -> name ^ ext  |> Find.prepend_output_dir
          | _ -> "out" ^ ext |> Find.prepend_output_dir
      in
      save_value_to_file oname bin

    | _ -> fail ()

let tc_one_file
        (env:uenv)
        (pre_fn:option string) //interface file name
        (fn:string) //file name
        (parsing_data:FStarC.Parser.Dep.parsing_data)  //passed by the caller, ONLY for caching purposes at this point
    : tc_result
    & option MLSyntax.mlmodule
    & uenv =
  Stats.record "tc_one_file" fun () ->
  GenSym.reset_gensym();

  (*
   * AR: this is common smt postprocessing for fresh module and module read from cache
   *)
  let restore_opts () : unit =
    Options.restore_cmd_line_options true |> ignore
  in
  let maybe_extract_mldefs tcmod env =
    match Options.codegen() with
    | None -> None, 0
    | Some tgt ->
      if not (Options.should_extract (string_of_lid tcmod.name) tgt)
      then None, 0
      else Timing.record_ms (fun () ->
            with_env env (fun env ->
              let _, defs = FStarC.Extraction.ML.Modul.extract env tcmod in
              defs)
          )
  in
  let maybe_extract_ml_iface tcmod env =
      if Options.codegen() = None
      then env, 0
      else
        Timing.record_ms (fun () ->
            let env, _ = with_env env (fun env ->
                  FStarC.Extraction.ML.Modul.extract_iface env tcmod) in
            env
          )
  in
  let tc_source_file () =
      let fmod, env = 
        Profiling.profile (fun () -> parse env pre_fn fn)
                          (Some (Parser.Dep.module_name_of_file fn))
                          "FStarC.Universal.tc_source_file.parse"  
      in
      let mii = FStarC.Syntax.DsEnv.inclusion_info (tcenv_of_uenv env).dsenv fmod.name in
      let check_mod () =
          let check env =
              if not (Options.lax()) then FStarC.SMTEncoding.Z3.refresh None;
              with_tcenv_of_env env (fun tcenv ->
                 let _ = match tcenv.gamma with
                         | [] -> ()
                         | _ -> failwith "Impossible: gamma contains leaked names"
                 in
                 let modul, env = Tc.check_module tcenv fmod (Some? pre_fn) in
                 //AR: encode the module to to smt
                 restore_opts ();
                 let smt_decls =
                   if not (Options.lax())
                   then FStarC.SMTEncoding.Encode.encode_modul env modul
                   else [], []
                 in
                 ((modul, smt_decls), env))
            in

          let ((tcmod, smt_decls), env) =
            Profiling.profile (fun () -> check env)
                              (Some (string_of_lid fmod.name))
                              "FStarC.Universal.tc_source_file.check"
          in

          let tc_time = 0 in
          let extracted_defs, extract_time = maybe_extract_mldefs tcmod env in
          let env, iface_extraction_time = maybe_extract_ml_iface tcmod env in
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
      SMT.with_hints_db (Pars.find_file fn) check_mod
  in
  if not (Options.cache_off()) then
      let r = Ch.load_module_from_cache (tcenv_of_uenv env) fn in
      let r =
        (* If --force and this file was given in the command line,
         * forget about the cache we just loaded and recheck the file.
         * Note: we do the call above anyway since load_module_from_cache
         * sets some internal state about dependencies.
         *
         * We do the same if we were called with --output and --cache_checked_modules
         * (-o, -c) and without codegen. This means the user is asking to generate a checked
         * file into the file provided by -o, so we should not be loading anything.
         * If codegen was given, the the user wants an ml/krml file, and it is fine
         * to load the cache.
         *)
        if Options.should_check_file fn && (
             Options.force () ||
             (Some? (Options.output_to ()) && None? (Options.codegen ()))
           )
        then None
        else r
      in
      match r with
      | None ->
        if Options.should_be_already_cached (FStarC.Parser.Dep.module_name_of_file fn)
        && not (Options.force ())
        then FStarC.Errors.raise_error0 FStarC.Errors.Error_AlreadyCachedAssertionFailure [
                 text <| Format.fmt1 "Expected %s to already be checked." fn
               ];

        if (Some? (Options.codegen())
        && Options.cmi())
        && not (Options.force ())
        then FStarC.Errors.raise_error0 FStarC.Errors.Error_AlreadyCachedAssertionFailure [
                 text "Cross-module inlining expects all modules to be checked first.";
                 text <| Format.fmt1 "Module %s was not checked." fn;
               ];

        let tc_result, mllib, env = tc_source_file () in

        if FStarC.Errors.get_err_count() = 0
        && (Options.lax()  //we'll write out a .checked.lax file
            || Options.should_verify (string_of_lid tc_result.checked_module.name)) //we'll write out a .checked file
        //but we will not write out a .checked file for an unverified dependence
        //of some file that should be checked
        //(i.e. we DO write .checked.lax files for dependencies even if not provided as an argument)
        then Ch.store_module_to_cache (tcenv_of_uenv env) fn parsing_data tc_result;
        tc_result, mllib, env

      | Some tc_result ->
        let tcmod = tc_result.checked_module in
        let smt_decls = tc_result.smt_decls in
        if Options.dump_module (string_of_lid tcmod.name)
        then Format.print1 "Module after type checking:\n%s\n" (show tcmod);

        let extend_tcenv tcmod tcenv =
            let _, tcenv =
                with_dsenv_of_tcenv tcenv <|
                    FStarC.ToSyntax.ToSyntax.add_modul_to_env
                        tcmod
                        tc_result.mii
                        (FStarC.TypeChecker.Normalize.erase_universes tcenv)
            in
            let env = FStarC.TypeChecker.Tc.load_checked_module tcenv tcmod in
            restore_opts ();
            //AR: encode smt module and do post processing
            if (not (Options.lax())) then begin
              FStarC.SMTEncoding.Encode.encode_modul_from_cache env tcmod smt_decls
            end;
            (), env
        in

        let env =
          Profiling.profile
            (fun () -> with_tcenv_of_env env (extend_tcenv tcmod) |> snd)
            None
            "FStarC.Universal.extend_tcenv"
        in


        (* If we have to extract this module, then do it first *)
        let mllib =
          match Options.codegen() with
          | None -> None
          | Some tgt ->
            if Options.should_extract (string_of_lid tcmod.name) tgt
            && (not tcmod.is_interface || tgt=Options.Krml)
            then let extracted_defs, _extraction_time = maybe_extract_mldefs tcmod env in
                 extracted_defs
            else None
        in

        let env, _time = maybe_extract_ml_iface tcmod env in

        tc_result,
        mllib,
        env

  else let tc_result, mllib, env = tc_source_file () in
       tc_result, mllib, env

let tc_one_file_for_ide
        (env:TcEnv.env_t)
        (pre_fn:option string) //interface file name
        (fn:string) //file name
        (parsing_data:FStarC.Parser.Dep.parsing_data)  //threaded along, ONLY for caching purposes at this point
    : tc_result
    & TcEnv.env_t
    =
    let env = env_of_tcenv env in
    let tc_result, _, env = tc_one_file env pre_fn fn parsing_data in
    tc_result, (tcenv_of_uenv env)

(***********************************************************************)
(* Batch mode: composing many files in the presence of pre-modules     *)
(***********************************************************************)
let needs_interleaving intf impl =
  let m1 = Parser.Dep.lowercase_module_name intf in
  let m2 = Parser.Dep.lowercase_module_name impl in
  m1 = m2 &&
  List.mem (Filepath.get_file_extension intf) ["fsti"; "fsi"] &&
  List.mem (Filepath.get_file_extension impl) ["fst"; "fs"]

let tc_one_file_from_remaining (remaining:list string) (env:uenv)
                               (deps:FStarC.Parser.Dep.deps)  //used to query parsing data
  : list string & tc_result & option MLSyntax.mlmodule & uenv
  =
  let remaining, (nmods, mllib, env) =
    match remaining with
        | intf :: impl :: remaining when needs_interleaving intf impl ->
          let m, mllib, env = tc_one_file env (Some intf) impl
                                          (impl |> FStarC.Parser.Dep.parsing_data_of deps) in
          remaining, (m, mllib, env)
        | intf_or_impl :: remaining ->
          let m, mllib, env = tc_one_file env None intf_or_impl
                                          (intf_or_impl |> FStarC.Parser.Dep.parsing_data_of deps) in
          remaining, (m, mllib, env)
        | [] -> failwith "Impossible: Empty remaining modules"
  in
  remaining, nmods, mllib, env

let rec tc_fold_interleave (deps:FStarC.Parser.Dep.deps)  //used to query parsing data
                           (acc:list tc_result &
                                list (uenv & MLSyntax.mlmodule) &  // initial env in which this module is extracted
                                uenv)
                           (remaining:list string) =
  let as_list env mllib =
    match mllib with
    | None -> []
    | Some mllib -> [env, mllib] in

  match remaining with
    | [] -> acc
    | _  ->
      let mods, mllibs, env_before = acc in
      let remaining, nmod, mllib, env = tc_one_file_from_remaining remaining env_before deps in
      if not (Options.profile_group_by_decl())
      then Profiling.report_and_clear (Ident.string_of_lid nmod.checked_module.name);
      tc_fold_interleave deps (mods@[nmod], mllibs@(as_list env mllib), env) remaining

(***********************************************************************)
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let dbg_dep = Debug.get_toggle "Dep"
let batch_mode_tc filenames dep_graph =
  if !dbg_dep then begin
    Format.print_string "Auto-deps kicked in; here's some info.\n";
    Format.print1 "Here's the list of filenames we will process: %s\n"
      (String.concat " " filenames);
    Format.print1 "Here's the list of modules we will verify: %s\n"
      (String.concat " " (filenames |> List.filter Options.should_verify_file))
  end;
  let env = FStarC.Extraction.ML.UEnv.new_uenv (init_env dep_graph) in
  let all_mods, mllibs, env = tc_fold_interleave dep_graph ([], [], env) filenames in
  if FStarC.Errors.get_err_count() = 0 then
    emit dep_graph mllibs;
  let solver_refresh env =
      snd <|
      with_tcenv_of_env env (fun tcenv ->
          if Options.interactive()
          && FStarC.Errors.get_err_count () = 0
          then tcenv.solver.refresh None
          else tcenv.solver.finish();
          (), tcenv)
  in
  all_mods, env, solver_refresh

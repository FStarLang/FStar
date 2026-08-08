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
open FStarC.Syntax.Print
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
module Ast      = FStarC.Parser.AST

let dbg_dep = Debug.get_toggle "Dep"

let module_or_interface_name m = m.is_interface, m.name

let with_dsenv_of_tcenv (tcenv:TcEnv.env) (f:DsEnv.withenv 'a) : ML ('a & TcEnv.env) =
    let a, dsenv = f tcenv.dsenv in
    a, ({tcenv with dsenv = dsenv})

let with_tcenv_of_env (e:uenv) (f:TcEnv.env -> ML ('a & TcEnv.env)) : ML ('a & uenv) =
     let a, t' = f (tcenv_of_uenv e) in
     a, (set_tcenv e t')

let with_dsenv_of_env (e:uenv) (f:DsEnv.withenv 'a) : ML ('a & uenv) =
     let a, tcenv = with_dsenv_of_tcenv (tcenv_of_uenv e) f in
     a, (set_tcenv e tcenv)

let push_env (env:uenv) : ML _ =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStarC.TypeChecker.Env.push (tcenv_of_uenv env) "top-level: push_env"))

let pop_env (env:uenv) : ML _ =
    snd (with_tcenv_of_env env (fun tcenv ->
            (), FStarC.TypeChecker.Env.pop tcenv "top-level: pop_env"))

let with_env env (f:uenv -> ML 'a) : ML 'a =
    let env = push_env env in
    let res = f env in
    let _ = pop_env env in
    res

(* When A.fsti is checked (or loaded from its .checked file) only in order to
   check A.fst, its SMT encoding must not be visible while checking A.fst: the
   interface encodes the module's abstract view (e.g. an abstract `val t : Type0`
   becomes an uninterpreted symbol, and an assumed `val` with an SMTPat becomes a
   live axiom), which clashes with --- and in the SMTPat case is unsound with
   respect to --- the definitions that the implementation encodes for the very
   same names. The interface sigelts that the implementation copies verbatim are
   encoded by the typechecker as it walks the to-do list.

   Its declarations reach the solver in two ways: incrementally, via
   [encode_sig], as the interface is checked declaration by declaration; and in
   one go via [encode_modul] at the end. We suppress the latter (see
   [encode_modul_no_solver]) and undo the former by rolling the solver back to a
   snapshot taken before the interface was processed.

   Rolling the solver back also undoes the encoding of the modules that were
   loaded on the fly while checking the interface, so we record them as we go and
   replay them right after the rollback. Frames nest: checking A.fsti may load a
   befriended module B, which in turn loads B.fsti in order to check B.fst. *)
let iface_solver_frames
  : ref (list (TcEnv.solver_depth_t &
               list (Syntax.modul & FStarC.SMTEncoding.Env.module_encoding)))
  = mk_ref []

(* Called at every point where a module's SMT encoding is handed to the solver. *)
let record_encoded_modul (m:Syntax.modul) smt_decls : ML unit =
  iface_solver_frames :=
    !iface_solver_frames |> List.map (fun (depth, pending) -> depth, (m, smt_decls) :: pending)

let push_iface_solver_frame (env:uenv) (name:string) : ML unit =
  let tcenv = tcenv_of_uenv env in
  let depth, () = tcenv.solver.snapshot name in
  iface_solver_frames := (depth, []) :: !iface_solver_frames

let pop_iface_solver_frame (env:uenv) (name:string) : ML unit =
  match !iface_solver_frames with
  | [] -> ()
  | (depth, pending) :: rest ->
    iface_solver_frames := rest;
    let tcenv = tcenv_of_uenv env in
    tcenv.solver.rollback name (Some depth);
    (* The interface's declarations left their names registered in the SMT name
       scope; free them so that the implementation encodes the very same lids
       under their canonical names. *)
    if not (Options.interactive ()) then FStarC.SMTEncoding.Env.varops.reset_scope ();
    (* Replay the encodings of the modules that were loaded on the fly while the
       interface was being processed; they are legitimate dependences. *)
    List.rev pending |> List.iter (fun (tcmod, smt_decls) ->
      if not (FStarC.SMTEncoding.Env.is_empty_encoding smt_decls)
      then FStarC.SMTEncoding.Encode.encode_modul_from_cache tcenv tcmod smt_decls;
      record_encoded_modul tcmod smt_decls)

let is_iface_of (fn:string) (root:option string) : ML bool =
  Dep.is_interface fn
  && (match root with
      | Some r ->
        Dep.is_implementation r
        && Dep.module_name_of_file r = Dep.module_name_of_file fn
      | None -> false)

let env_of_tcenv (env:TcEnv.env) : ML _ =
    FStarC.Extraction.ML.UEnv.new_uenv env

(***********************************************************************)
(* Parse and maybe interleave & desugar a file with its interface      *)
(***********************************************************************)
let parse (fly_deps:bool) (env:uenv) (fn:string)
  : ML (lident
  & either FStarC.Parser.AST.modul FStarC.Syntax.Syntax.modul
  & uenv) =
  let ast, _ = Parser.Driver.parse_file fn in
  if fly_deps
  then Ast.lid_of_modul ast, Inl ast, env
  else let mod, env = with_dsenv_of_env env (Desugar.ast_modul_to_modul ast) in
       Ast.lid_of_modul ast, Inr mod, env


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
    

(***********************************************************************)
(* Interactive mode: checking a fragment of a code                     *)
(***********************************************************************)
module Ast = FStarC.Parser.AST
let parse_frag frag lang_decls : ML _ =
  let open FStarC.Parser.AST in
  let use_lang_decl (ds:lang_decls_t) =
    List.tryFind (fun d -> UseLangDecls? d.d) ds
  in
  match use_lang_decl lang_decls with
  | None -> Parser.Driver.parse_fragment None frag
  | Some {d=UseLangDecls lang} ->
    Parser.Driver.parse_fragment (Some lang) frag

//This is the main driver of the typechecker, checking one declaration at a time    
let tc_one_fragment is_interface curmod (env:TcEnv.env_t) frag
  : ML _ =
  let open FStarC.Parser.AST in
  let fname env = List.hd (Options.file_list ()) in
  let acceptable_mod_name ast_modul =
    (* Interface is sent as the first chunk, so we must allow repeating the same module. *)
    Parser.Dep.lowercase_module_name (fname env) =
    String.lowercase (string_of_lid (Ast.lid_of_modul ast_modul)) in

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
  let check_module_name_declaration ast_modul = 
      (* It may seem surprising that this function, whose name indicates that
         it type-checks a fragment, can actually parse an entire module.
         Actually, this is an abuse, and just means that we're type-checking the
         first chunk. *)
      if not (acceptable_mod_name ast_modul) then
      begin
        let msg : string =
            Format.fmt1 "Interactive mode only supports a single module at the top-level. Expected module %s"
                                    (Parser.Dep.module_name_of_file (fname env))
        in
        Errors.raise_error (range_of_first_mod_decl ast_modul) Errors.Fatal_NonSingletonTopLevelModule msg
      end;
      let modul, env =
          if DsEnv.syntax_only env.dsenv 
          then with_dsenv_of_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul
          else (
            let m, env = with_dsenv_of_tcenv env <| Desugar.partial_ast_modul_to_modul curmod ast_modul in
            Tc.tc_partial_modul env m
          )

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
      let modul, _, env  = 
        if DsEnv.syntax_only env.dsenv 
        then let _, env = with_dsenv_of_tcenv env <| Desugar.decls_to_sigelts ast_decls in
             (modul, [], env)
        else (
          let ses, env = 
          Errors.with_ctx ("While desugaring module " ^ Class.Show.show (modul.name)) (fun _ -> 
            with_dsenv_of_tcenv env <| Desugar.decls_to_sigelts ast_decls
          ) in
          Tc.tc_more_partial_modul env modul ses
        ) 
      in

      Some modul, env, List.filter filter_lang_decls ast_decls
  in
  match frag with
  | Inr d -> (
    if Debug.low() then Format.print1 "tc_one_fragment: %s\n" (show d);
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
      let modul = if is_interface then Ast.as_interface modul else modul in
      check_module_name_declaration modul
    | _ -> 
      check_decls [d]
  )

  | Inl (frag, lang_decls) -> (
    match parse_frag frag lang_decls with
    | Parser.Driver.Empty
    | Parser.Driver.Decls [] ->
      curmod, env, []

    | Parser.Driver.Modul ast_modul ->
      check_module_name_declaration ast_modul

    | Parser.Driver.Decls ast_decls ->
      check_decls ast_decls
  )
    
(***********************************************************************)
(* Batch mode: checking a file                                         *)
(***********************************************************************)

(* Extraction to OCaml, F# or Krml *)
let emit dep_graph (mllib : list (uenv & MLSyntax.mlmodule)) : ML unit =
  let opt = Options.codegen () in
  let fail #a () : ML a = failwith ("Unrecognized extraction backend: " ^ show opt) in
  if opt <> None then
    let ext = match opt with
      | Some Options.FSharp -> ".fs"
      | Some Options.OCaml
      | Some Options.Plugin -> ".ml"
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
    | Some Options.FSharp | Some Options.OCaml | Some Options.Plugin ->
      let printer : MLSyntax.mlmodule -> ML string =
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
      (* An interface and its implementation are two separately checked modules
         but a single Karamel program: the checked implementation already
         contains the declarations copied from the interface. Keep only the
         last program for each name, i.e. the implementation's. *)
      let programs =
        let rec dedup seen ps : ML _ =
          match ps with
          | [] -> []
          | (name, decls)::ps ->
            if seen |> List.existsb (fun n -> n = name)
            then dedup seen ps
            else (name, decls) :: dedup (name::seen) ps
        in
        List.rev (dedup [] (List.rev programs))
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

let rec tc_one_file_internal
        (fly_deps:bool)
        (skip_solver:bool) (* this module's encoding must not survive the call *)
        (env:uenv)
        (fn:string) //file name
    : ML (tc_result
    & option MLSyntax.mlmodule
    & uenv) =
  if skip_solver
  then (
    let name = "interface of " ^ Dep.module_name_of_file fn in
    push_iface_solver_frame env name;
    let res = tc_one_file_no_frame fly_deps true env fn in
    pop_iface_solver_frame env name;
    res
  )
  else tc_one_file_no_frame fly_deps false env fn

and tc_one_file_no_frame
        (fly_deps:bool)
        (skip_solver:bool)
        (env:uenv)
        (fn:string)
    : ML (tc_result
    & option MLSyntax.mlmodule
    & uenv) =
  Stats.record "tc_one_file" fun () ->
  GenSym.reset_gensym();

  (*
   * AR: this is common smt postprocessing for fresh module and module read from cache
   *)
  let restore_opts () : ML unit =
    Options.restore_cmd_line_options true |> ignore
  in
  let maybe_extract_mldefs tcmod env : ML _ =
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
  let maybe_extract_ml_iface tcmod env : ML _ =
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
      let mname, fmod, env = 
        Profiling.profile (fun () -> parse fly_deps env fn)
                          (Some (Parser.Dep.module_name_of_file fn))
                          "FStarC.Universal.tc_source_file.parse"  
      in
      let check_mod () =
          let check env =
            FStarC.SMTEncoding.Z3.refresh None;
            let modul, env =
              if fly_deps
              then let Inl ast_mod = fmod in
                    fly_deps_check fn env ast_mod
              else let Inr mod = fmod in
                    with_tcenv_of_env env (fun tcenv -> Tc.check_module tcenv mod)
            in
              //AR: encode the module to to smt
            restore_opts ();
            let smt_decls =
              if skip_solver
              then FStarC.SMTEncoding.Encode.encode_modul_no_solver (tcenv_of_uenv env) modul
              else FStarC.SMTEncoding.Encode.encode_modul (tcenv_of_uenv env) modul
            in
            if not skip_solver then record_encoded_modul modul smt_decls;
            ((modul, smt_decls), env)
          in

          let ((tcmod, smt_decls), env) =
            Profiling.profile (fun () -> check env)
                              (Some (string_of_lid mname))
                              "FStarC.Universal.tc_source_file.check"
          in

          let tc_time = 0 in
          let extracted_defs, extract_time = maybe_extract_mldefs tcmod env in
          let env, iface_extraction_time = maybe_extract_ml_iface tcmod env in
          let pd =
            let deps = TcEnv.dep_graph (tcenv_of_uenv env) in
            match fmod with
            | Inl ast_mod ->
              Dep.parsing_data_of_modul deps fn (Some ast_mod)
            | Inr mod ->
              let pd = Dep.parsing_data_of deps fn in
              pd, Dep.deps_of deps fn 

          in
          let mii = FStarC.Syntax.DsEnv.inclusion_info (tcenv_of_uenv env).dsenv mname in
          pd,
          {
            checked_module=tcmod;
            tc_time=tc_time;
            smt_encoding=smt_decls;

            extraction_time = extract_time + iface_extraction_time;
            mii = mii
          },
          extracted_defs,
          env
      in
      SMT.with_hints_db (Pars.find_file fn) 
        check_mod
  in
  if not (Options.cache_off()) then
      let r = 
        if fly_deps && Options.should_check_file fn
        then None //if we reach here with fly_deps, then checked files are invalid
        else Ch.load_module_from_cache (tcenv_of_uenv env) fn
      in
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

        let parsing_data, tc_result, mllib, env = tc_source_file () in

        if FStarC.Errors.get_err_count() = 0
        && Options.should_write_checked_file fn
        then begin
          Ch.store_module_to_cache (tcenv_of_uenv env) fn parsing_data tc_result
        end;
        tc_result, mllib, env

      | Some tc_result ->
        let tcmod = tc_result.checked_module in
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
            if not skip_solver then
              (* Deferred: reading this module's SMT encoding out of its checked
                 file, and handing it to the solver, is pure waste if we never
                 issue a query. See FStarC.SMTEncoding.Encode.defer_encoding. *)
              FStarC.SMTEncoding.Encode.defer_encoding (fun () ->
                let smt_decls = tc_result.smt_encoding in
                if not (FStarC.SMTEncoding.Env.is_empty_encoding smt_decls) then
                  FStarC.SMTEncoding.Encode.encode_modul_from_cache env tcmod smt_decls;
                record_encoded_modul tcmod smt_decls
              );
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

  else let _, tc_result, mllib, env = tc_source_file () in
       tc_result, mllib, env

and fly_deps_check (filename:string) (env:uenv) (ast_mod:Ast.modul) : ML (Syntax.modul & uenv) =
  let decls = Ast.decls_of_modul ast_mod in
  let mname = match decls with
    | {d=Ast.TopLevelModule lid} :: rest -> lid
    | _ -> failwith "Impossible: first decl is not a module"
  in
  if Dep.debug_fly_deps() then Format.print1 "Before fly load deps: %s\n" (FStarC.Pprint.render <| FStarC.Class.PP.pp decls);
  Dep.populate_parsing_data filename ast_mod (DsEnv.dep_graph (tcenv_of_uenv env).dsenv);
  let is_interface = FStarC.Parser.Dep.is_interface filename in
  (* A `friend M` declaration must be honoured before anything else pulls in the
     interface of M --- in particular before this module's own interface, which
     is loaded when the module header is scanned. So resolve the friends first. *)
  let env =
    decls |> List.fold_left (fun env d ->
      match d.Ast.d with
      | Ast.Friend _ -> fst (scan_and_load_fly_deps_internal filename env (Inr d))
      | _ -> env) env
  in
  let mod, env =
    List.fold_left
      (fun (mod, env) decl ->
        if Dep.debug_fly_deps() 
        then Format.print1 "fly_deps_check next decl: %s\n" 
          (FStarC.Pprint.render <| FStarC.Class.PP.pp decl);
        
        let env, _ = scan_and_load_fly_deps_internal filename env (Inr decl) in
        let mod, env = 
          with_tcenv_of_env env
            (fun tcenv -> 
              let mod, tcenv, _ = tc_one_fragment is_interface mod tcenv (Inr decl) in
              mod, tcenv)
        in
        mod, env)
      (None, env)
      decls 
  in
  if None? mod then failwith "Impossible";
  let Some mod = mod in
  let mod, env =
    with_tcenv_of_env env (fun tcenv ->
      let dsenv, mod = DsEnv.finish_module_or_interface tcenv.dsenv mod in
      let tcenv = {tcenv with dsenv=dsenv} in
      Tc.finish_partial_modul false false tcenv mod) in
  mod, env

and scan_and_load_fly_deps_internal filename (env:uenv) frag_or_decl: ML (uenv & list string) =
  let load_fly_deps (env:uenv) filenames =
    match filenames with
    | [] -> env //if nothing to load, just return to avoid resetting solver, etc.
    | _ ->
      let run_load_tasks env filenames =
        let _, _, env = tc_fold_interleave false (Some filename) ([], [], env) filenames in
        env
      in
      let _, env = 
        //load modules clearing out the current local environment, and then
        //restore it. The global environment is accumulated, e.g., containing
        //all modules desugared and extracted so far. This is key to fly_deps. 
        FStarC.Extraction.ML.UEnv.with_restored_tc_scope env 
          (fun env -> (), run_load_tasks env filenames) 
      in
      if Dep.debug_fly_deps() then Format.print1 "After fly load deps: %s\n" (show (tcenv_of_uenv env).dsenv);
      env
  in
  let scan_fragment_deps env frag_or_decl =
    let deps = FStarC.Syntax.DsEnv.dep_graph env.dsenv in
    let deps = FStarC.Parser.Dep.copy_deps deps in
    let env = { env with dsenv=FStarC.Syntax.DsEnv.set_dep_graph env.dsenv deps } in
    let decls = 
      match frag_or_decl with
      | Inl (frag, lang_decls) -> (
        let dfrag = parse_frag frag lang_decls in
        match dfrag with
        | Parser.Driver.Empty
        | Parser.Driver.Decls [] -> []

        | Parser.Driver.Modul ast_modul ->
          Ast.decls_of_modul ast_modul
        
        | Parser.Driver.Decls decls -> decls
      )
      | Inr d -> [d]
    in
    let filenames_to_load =
      FStarC.Parser.Dep.collect_deps_of_decl
        deps
        filename
        decls
        (DsEnv.parsing_data_for_scope env.dsenv)
        FStarC.CheckedFiles.load_parsing_data_from_cache
    in
    if Dep.debug_fly_deps() then (
      Format.print1 "Initial files loaded: %s\n" (show <| FStarC.Parser.Dep.all_files deps);
      Format.print1 "Decls scanned: %s\n" (show decls);
      Format.print1 "Additional files to load: %s\n" (show filenames_to_load)
    );
    let filenames = List.filter (fun fn -> fn <> filename) <| List.rev filenames_to_load in
    (* Files whose module is already in the environment need not (and must not)
       be loaded again. The one case that is a genuine error is a `friend`
       declaration on a module of which only the interface has been loaded:
       the implementation cannot be revealed after the fact. *)
    let already_loaded fn =
      let mname = Dep.module_name_of_file fn in
      env.modules |> List.filter (fun m -> mname = Ident.string_of_lid m.name)
    in
    let filenames =
      filenames |> List.filter (fun fn ->
        match already_loaded fn with
        | [] -> true
        | ms ->
          if Dep.is_implementation fn && not (ms |> List.existsb (fun m -> not m.is_interface))
          then
            raise_error (Env.get_range env) Errors.Fatal_CyclicDependence [
              text "Friend dependences must be declared as the first dependence on a module.";
              text (Format.fmt1 "A non-friend dependence was already found on module %s." (Dep.module_name_of_file fn))
            ]
          else false)
    in
    filenames, env
  in  
  let filenames, env = with_tcenv_of_env env (fun tcenv -> scan_fragment_deps tcenv frag_or_decl) in
  let env = load_fly_deps env filenames in
  env, filenames

and tc_one_file_from_remaining 
      (fly_deps:bool)
      (root:option string) (* the file we are ultimately going to check, if any *)
      (remaining:list string) 
      (env:uenv)
: ML (list string & tc_result & option MLSyntax.mlmodule & uenv) =
  let remaining, (nmods, mllib, env) =
    match remaining with
        | intf_or_impl :: rest ->
          let mname = Dep.module_name_of_file intf_or_impl in
          (* Is this the interface of the module whose implementation we are
             about to check --- either the very next file in this batch, or the
             root file for which the on-the-fly dependences are being loaded? *)
          let skip_solver =
            is_iface_of intf_or_impl root
            || (Dep.is_interface intf_or_impl
                && (match rest with
                    | next :: _ -> not (Dep.is_interface next) && Dep.module_name_of_file next = mname
                    | [] -> false))
          in
          let m, mllib, env = tc_one_file_internal fly_deps skip_solver env intf_or_impl in
          rest, (m, mllib, env)
        | [] -> failwith "Impossible: Empty remaining modules"
  in
  remaining, nmods, mllib, env

and tc_fold_interleave
      (fly_deps:bool) 
      (root:option string)
      (acc:list tc_result &
           list (uenv & MLSyntax.mlmodule) &  // initial env in which this module is extracted
           uenv)
      (remaining:list string)
: ML (list Ch.tc_result & list (uenv & MLSyntax.mlmodule) & uenv) =
  let as_list env mllib =
    match mllib with
    | None -> []
    | Some mllib -> [env, mllib] in
  match remaining with
    | [] -> acc
    | _  ->
      let mods, mllibs, env_before = acc in
      let remaining, nmod, mllib, env = tc_one_file_from_remaining fly_deps root remaining env_before in
      if not (Options.profile_group_by_decl())
      then Profiling.report_and_clear (Ident.string_of_lid nmod.checked_module.name);
      tc_fold_interleave fly_deps root (mods@[nmod], mllibs@(as_list env mllib), env) remaining


let load_file
        (env:TcEnv.env_t)
        (fn:string) //file name
: ML TcEnv.env_t
= let env = env_of_tcenv env in
  let tc_result, _, env = tc_one_file_internal false false env fn in
  tcenv_of_uenv env

(* Load the interface of the file currently being edited in interactive mode.
   Its SMT encoding must not be visible while checking the implementation. *)
let load_interface_of_current_file (env:TcEnv.env_t) (fn:string) : ML TcEnv.env_t
= let uenv = env_of_tcenv env in
  let _, _, uenv = tc_one_file_internal false true uenv fn in
  tcenv_of_uenv uenv

let scan_and_load_fly_deps
    (filename:string)
    (env:TcEnv.env_t)
    (input:either (FStarC.Parser.ParseIt.input_frag & lang_decls_t) FStarC.Parser.AST.decl)
  : ML _ = let uenv, files = scan_and_load_fly_deps_internal filename (new_uenv env) input in
  tcenv_of_uenv uenv, files

let load_fly_deps_and_tc_one_fragment
    (filename:string)
    (is_interface:bool)
    (mod:option Syntax.modul)
    (tcenv:TcEnv.env_t)
    (frag_or_decl:either (FStarC.Parser.ParseIt.input_frag & lang_decls_t) FStarC.Parser.AST.decl)
: ML (option Syntax.modul &
  TcEnv.env &
  lang_decls_t &
  list string) //filenames that were loaded
= //parse, if needed
  let ast_decls = 
    match frag_or_decl with
    | Inl (frag, lang_decls) -> (
      let dfrag = parse_frag frag lang_decls in
      match dfrag with
      | Parser.Driver.Empty
      | Parser.Driver.Decls [] -> []

      | Parser.Driver.Modul ast_modul ->
        Ast.decls_of_modul ast_modul
      
      | Parser.Driver.Decls decls -> decls
    )
    | Inr d -> [d]
  in
  //scan and check, one by one
  let (tcenv, curmod), langs_filenames =
    BU.fold_map
      (fun (tcenv, curmod) a_decl -> 
        let tcenv, filenames = scan_and_load_fly_deps filename tcenv (Inr a_decl) in
        let curmod, tcenv, langs = tc_one_fragment is_interface curmod tcenv (Inr a_decl) in
        (tcenv, curmod), (langs, filenames))
      (tcenv, mod)
      ast_decls
  in
  let langs_l, filenames_l = List.unzip langs_filenames in
  curmod, tcenv, List.flatten langs_l, List.flatten filenames_l


(***********************************************************************)
(* Initialize a clean environment                                      *)
(***********************************************************************)
let init_env deps : ML TcEnv.env =
  let solver =
    {SMT.solver with
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
(* Batch mode: checking many files                                     *)
(***********************************************************************)
let batch_mode_tc fly_deps filenames dep_graph
  : ML _ =
  if !dbg_dep then begin
    Format.print_string "Auto-deps kicked in; here's some info.\n";
    Format.print1 "Here's the list of filenames we will process: %s\n"
      (String.concat " " filenames);
    Format.print1 "Here's the list of modules we will verify: %s\n"
      (String.concat " " (filenames |> List.filter Options.should_verify_file))
  end;
  let env = FStarC.Extraction.ML.UEnv.new_uenv (init_env dep_graph) in
  let all_mods, mllibs, env = tc_fold_interleave fly_deps None ([], [], env) filenames in
  if FStarC.Errors.get_err_count() = 0 then
    emit dep_graph mllibs;
  let solver_refresh env =
      snd <|
      with_tcenv_of_env env (fun tcenv ->
         tcenv.solver.finish();
        (), tcenv)
  in
  all_mods, env, solver_refresh

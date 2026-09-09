(*
   Copyright 2008-2018 Microsoft Research

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

module FStarC.CheckedFiles
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC
open FStarC.Effect
open FStarC.SMap

open FStarC.Class.Show

(* Module abbreviations for the universal type-checker  *)
module Syntax  = FStarC.Syntax.Syntax
module TcEnv   = FStarC.TypeChecker.Env
module BU      = FStarC.Util
module Dep     = FStarC.Parser.Dep
open FStarC.SMTEncoding.Term
open FStarC.SMTEncoding.Env

let dbg = Debug.get_toggle "CheckedFiles"
let debug (f:unit -> ML unit) : ML unit = if !dbg then f () else ()

(*
 * We write this version number to the cache files, and
 * detect when loading the cache that the version number is same
 *)
let cache_version_number = 97

(*
 * Abbreviation for what we store in the checked files (stages as described below)
 *)
type checked_file_entry_stage1 =
{
  //cache version number
  version: int;

  //digest of this source file to check if parsing data is valid
  digest: string;

  //parsing data for this file
  parsing_data: Parser.Dep.parsing_data
}

//The persisted part of a tc_result. The SMT encoding's declarations are not
//included: they are written as a third value in the checked file so that they
//can be read on demand. Their index is small and is stored here, since it is
//needed as soon as the module is loaded.
type tc_result_stored =
{
  stored_checked_module: Syntax.modul;
  stored_mii: DsEnv.module_inclusion_info;
  stored_smt_index: list FStarC.SMTEncoding.Pruning.elt_summary;
  stored_smt_fvbs: list FStarC.SMTEncoding.Env.fvar_binding
}

type checked_file_entry_stage2 =
{
  //list of (file_name * digest) of direct dependences
  //file_name is name of the source file and
  //digest is that of the corresponding checked file
  //except when the entries are for the current .fst and .fsti,
  //digest is that of the source file
  deps_dig: list (string & string);

  //typechecking result, excluding the smt encoding
  tc_res: tc_result_stored
}

(*
 * Local cache for checked files contents
 * Note that a checked file could have valid parsing data but stale tc data
 *)

(*
 * Cache files could be loaded in two steps
 *
 * Initially the dependence analysis is just interested in the parsing data
 *   and till that point we don't have the dependences sorted out, because of
 *   which we can't check the validity of tc data (since we need to check hashes
 *   of direct dependences etc.)
 *
 * So in this step, we read the checked file and mark the validity if tc data as Unknown
 *
 * Later on, we have figured the complete dependence graph, and want to load
 *   the tc data
 *
 *  At that point, the cache is updated to either Valid or Invalid w.r.t. the tc data
 *)
type tc_result_t =
  | Unknown of string  //digest of the checked file; validity of the tc data not yet determined
  | Invalid of string  //reason why this is invalid
  | Valid   of string  //digest of the checked file

instance _ : showable tc_result_t = {
  show = (function Unknown s -> "Unknown " ^ show s
                 | Invalid s -> "Invalid " ^ show s
                 | Valid   s -> "Valid " ^ show s);
}

(*
 * The cache of checked files
 *)
type cache_t =
  tc_result_t &  //tc data part

  //either: reason why this checked file is not valid for parsing data
  //or    : parsing_data
  either string Dep.parsing_data

//Internal cache
let mcache : smap cache_t = SMap.create 50
let add_and_return checked_fn elt = 
  SMap.add mcache checked_fn elt; elt
let try_find_in_cache checked_fn = SMap.try_find mcache checked_fn
let dump_cache_keys tag = 
  if !dbg then Format.print2 "(%s) Cache contains %s\n" tag (show (SMap.keys mcache))
 

(*
 * Load a checked file into the cache
 *
 * This is loading the parsing data, and tc data as Unknown (unless checked file is invalid)
 *
 * See above for the two steps of loading the checked files
 *)
let load_checked_file (fn:string) (checked_fn:string) : ML cache_t =
  debug (fun _ ->
      Format.print1
        "Trying to load checked file result %s\n"
        checked_fn);
  let elt = checked_fn |> try_find_in_cache in
  if elt |> Some?
  then (
    //already loaded
    elt |> Option.must
  ) else
    let add_and_return = add_and_return checked_fn in
    if not (Filepath.file_exists checked_fn)
    then let msg = Format.fmt1 "checked file %s does not exist" checked_fn in
         add_and_return (Invalid msg, Inl msg)
    else let entry :option (string & checked_file_entry_stage1) = BU.load_1value_from_file3 checked_fn in
         match entry with
         | None ->
           let msg = Format.fmt1 "checked file %s is corrupt" checked_fn in
           add_and_return (Invalid msg, Inl msg)
         | Some (checked_digest, x) ->
           if x.version <> cache_version_number
           then let msg = Format.fmt1 "checked file %s has incorrect version" checked_fn in
                add_and_return (Invalid msg, Inl msg)
           else let current_digest = BU.digest_of_file fn in
                if x.digest <> current_digest
                then begin
                  debug (fun _ ->
                    Format.print4 "Checked file %s is stale since incorrect digest of %s, \
                      expected: %s, found: %s\n"
                      checked_fn fn current_digest x.digest);
                  let msg = Format.fmt2 "checked file %s is stale (digest mismatch for %s)" checked_fn fn in
                  add_and_return (Invalid msg, Inl msg)
                end
                else add_and_return (Unknown checked_digest, Inr x.parsing_data)

(*
 * Either the reason because of which dependences are stale/invalid
 *   or the list of dep string, as defined in the checked_file_entry above
 *)
let hash_dependences (deps:Dep.deps) (fn:string) (deps_of_fn:list string): ML (either string (list (string & string))) =
  Stats.record "hash_dependences" fun () ->
  let fn =
    match Find.find_file fn with
    | Some fn -> fn
    | _ -> fn
  in
  let module_name = Dep.lowercase_module_name fn in
  let source_hash = BU.digest_of_file fn in
  let has_interface = Some? (Dep.interface_of deps module_name) in
  let interface_source_file_name =
    if Dep.is_implementation fn
    && has_interface
    then module_name
      |> Dep.interface_of deps
    else None
  in
  let binary_deps = deps_of_fn
    |> List.filter (fun fn ->
         not (Dep.is_interface fn &&
              Dep.lowercase_module_name fn = module_name)) in
  let binary_deps =
    FStarC.List.sortWith
      (fun fn1 fn2 ->
       String.compare (Dep.lowercase_module_name fn1)
                      (Dep.lowercase_module_name fn2))
    binary_deps in
  (* The implementation's checked file records the digest of its interface's
     *source*, not of the interface's checked file. Every dependence of the
     interface is also a dependence of the implementation, so they are already
     accounted for in [binary_deps]; and the interface's checked file may
     legitimately have been produced under a different dependence graph (e.g.
     one where the implementation's `friend` declarations did not widen an
     interface dependence into a dependence on an implementation). *)
  let maybe_add_iface_hash out =
    match interface_source_file_name with
    | None -> Inr (("source", source_hash)::out)
    | Some iface ->
      let iface =
        match Find.find_file iface with
        | Some f -> f
        | None -> iface
      in
      Inr (("source", source_hash)::("interface", BU.digest_of_file iface)::out)
  in

  let rec hash_deps out (l:list string) : ML (either string (list (string & string))) = match l with
  | [] -> maybe_add_iface_hash out
  | fn::deps ->
    let cache_fn = Dep.cache_file_name fn in
    (*
     * It is crucial to get the digest of fn from cache, rather than computing it directly
     * See #1668
     *)
    let digest =
      match try_find_in_cache cache_fn with
      | None ->
        let msg = Format.fmt2 "For dependency %s, cache file %s is not loaded" fn cache_fn in
        debug (fun _ -> Format.print1 "%s\n" msg);
        Inl msg
      | Some (Invalid msg, _) -> Inl msg
      | Some (Valid dig, _)   -> Inr dig
      | Some (Unknown _, _)   ->
        failwith (Format.fmt2
                    "Impossible: unknown entry in the cache for dependence %s of module %s"
                    fn module_name)
    in
    match digest with
    | Inl msg -> Inl msg
    | Inr dig ->
      let mn = Dep.lowercase_module_name fn in
      hash_deps ((mn, dig) :: out) deps
  in
  hash_deps [] binary_deps


(* Reads the declarations of the SMT encoding of [checked_fn] -- the third value
   in the file -- and memoizes the result, so that they are read at most once
   even if the thunk is forced repeatedly. *)
let smt_decls_thunk (checked_fn:string) : ML (unit -> ML decls_t) =
  let memo : ref (option decls_t) = mk_ref None in
  fun () ->
    match !memo with
    | Some d -> d
    | None ->
      let d =
        match BU.load_3rd_value_from_file3 #decls_t checked_fn with
        | Some d -> d
        | None ->
          failwith (Format.fmt1 "Could not read the SMT encoding from checked file %s" checked_fn)
      in
      memo := Some d;
      d

let tc_result_of_stored (checked_fn:string) (s:tc_result_stored) : ML tc_result =
  { checked_module = s.stored_checked_module;
    mii = s.stored_mii;
    smt_encoding = { me_index = s.stored_smt_index;
                     me_fvbs = s.stored_smt_fvbs;
                     me_decls = smt_decls_thunk checked_fn };
    tc_time = 0;
    extraction_time = 0 }

let load_tc_result (checked_fn:string) : ML (option (list (string & string) & tc_result)) =
  let entry : option (string & checked_file_entry_stage1 & checked_file_entry_stage2) =
    BU.load_2values_from_file3 checked_fn
  in
  match entry with
  | Some ((_,_,s2)) -> Some (s2.deps_dig, tc_result_of_stored checked_fn s2.tc_res)
  | _ -> None

(*
 * Second step for loading checked files, validates the tc data
 * Either the reason why tc_result is invalid
 *   or tc_result
 *)
let load_checked_file_with_tc_result
  (deps:Dep.deps)
  (fn:string)
  (checked_fn:string)
  : ML (either string tc_result)
=
  debug (fun _ -> Format.print1 "Trying to load checked file with tc result %s\n" checked_fn);

  (* The first phase of the load only reads the head of the checked file. A
     concurrent fstar.exe sharing this --cache_dir may replace the file in
     between the two phases, in which case reading the rest of it fails. That
     is not an internal error: just record the entry as invalid, so that the
     caller rechecks the module. *)
  let vanished () : ML (either string tc_result) =
    let msg = Format.fmt1 "checked file %s changed while it was being read" checked_fn in
    let _ = add_and_return checked_fn (Invalid msg, Inl msg) in
    Inl msg
  in

  let elt = load_checked_file fn checked_fn in  //first step, in case some client calls it directly
  match elt with
  | Invalid msg, _ -> Inl msg
  | Valid _, _ -> (
    match load_tc_result checked_fn with
    | None -> vanished ()
    | Some (_, tc_result) -> Inr tc_result
  )
  | Unknown checked_digest, parsing_data ->
    match hash_dependences deps fn (Dep.deps_of deps fn) with
    | Inl msg ->
      let elt = (Invalid msg, parsing_data) in
      let _ = add_and_return checked_fn elt in
      Inl msg
    | Inr deps_dig' ->
    match load_tc_result checked_fn with
    | None -> vanished ()
    | Some (deps_dig, tc_result) ->
      let module_name = fn |> Dep.module_name_of_file in
      if deps_dig = deps_dig'
      || Options.should_be_already_cached module_name
      then begin
        //mark the tc data of the file as valid
        let elt = (Valid checked_digest, parsing_data) in
        let _ = add_and_return checked_fn elt in
        (*
         * if there exists an interface for it, mark that too as valid
         * this is specially needed for extraction invocations of F* with --cmi flag
         * for example, consider a scenario:
         * A.fst -> B.fsti -> Prims.fst
         *            ^      ^
         *            |     /
         *             B.fst
         *
         * when all the checked files are present and F* is invoked with --extract A --cmi
         * during parsing, all checked files are loaded with tc data statemachine as Unknown
         * since it is cmi (and say B has an inline_for_extraction symbol), the client
         * then loads B.fst.checked BUT NOT B.fsti.checked
         * this advances the state machine for B.fst, but not for B.fsti
         * so when client loads A.fst.checked, B.fsti -- a dependence of A -- is still in Unknown
         * following code relies on the invariant that:
         * validity of implementaton tc data implies validity of iface tc data
         *
         * an alternative is to not do this, but in hash_dependences, if some dependence
         * is in Unknown state, it could call load_checked_file_with_tc_result
         *)
        let validate_iface_cache () =
          let iface = fn |> Dep.lowercase_module_name |> Dep.interface_of deps in
          match iface with
          | None -> ()
          | Some iface ->
            try
              let iface_checked_fn = iface |> Dep.cache_file_name in
              match try_find_in_cache iface_checked_fn with
              | Some (Unknown iface_digest, parsing_data) ->
                let _ = add_and_return iface_checked_fn (Valid iface_digest, parsing_data) in
                ()
              | _ -> ()
            with
              | _ -> ()
        in
        validate_iface_cache ();
        Inr tc_result
      end
      else begin
        debug (fun _ ->
          Format.print4 "FAILING to load.\nHashes computed (%s):\n%s\n\nHashes read (%s):\n%s\n"
            (show (List.length deps_dig'))
            (FStarC.Parser.Dep.print_digest deps_dig')
            (show (List.length deps_dig))
            (FStarC.Parser.Dep.print_digest deps_dig);
          if List.length deps_dig = List.length deps_dig'
          then List.iter2 (fun (x,y) (x', y') ->
                 if x<>x' || y<>y'
                 then Format.print2 "Differ at: Expected %s\n Got %s\n"
                                (FStarC.Parser.Dep.print_digest [(x,y)])
                                (FStarC.Parser.Dep.print_digest [(x',y')])) deps_dig deps_dig'
        );
        let msg =
          Format.fmt1
            "checked file %s is stale (dependence hash mismatch, use --debug CheckedFiles for more details)"
            checked_fn
        in
        let elt = (Invalid msg, Inl msg) in
        let _ = add_and_return checked_fn elt in
        Inl msg
      end


let load_parsing_data_from_cache file_name : ML (option Parser.Dep.parsing_data) =
  (*
   * the code below suppresses the already_cached assertion failure
   * following is the reason for it:
   *
   * consider a scenario:
   * A.fst -> B.fsti -> Prims.fst
   *            ^      ^
   *            |     /
   *             B.fst
   *
   * the dependence analysis marks B.fsti as a dependence of A.fst
   * so when we use the makefiles to build this,
   *   makefile could first build prims, then B.fsti, and then tried to build A.fst
   *   with: fstar.exe A.fst already_cached '* -A'
   * now F* starts to build the dependence graph for A
   * it sees that A depends on B, so it reads the parsing data
   *   of B.fsti from its existing checked file
   * however, the dependence analysis ALSO reads B.fst so as to detect cycles
   * and calls load_parsing_data_from_cache_file with B.fst
   * clearly until this point, B.fst has not been checked and so its checked file doesn't exist
   * so cache_file_name raises an exception since B is in the already_cached list
   *
   * suppressing the exception here is not too bad since this exception is raised at other places
   *   e.g. when loading the checked file for typechecking purposes
   *
   * another way to handle this kind of thing would be to NOT load B.fst for cycle detection,
   *   rather provide a separate F* command --detect_cycles --alredy_cached '*' that builds
   *   can invoke in the end for cycle detection
   *)
  Errors.with_ctx ("While loading parsing data from " ^ file_name) (fun () ->
  let cache_file =
    try
     Parser.Dep.cache_file_name file_name |> Some
    with _ -> None
  in
  match cache_file with
  | None -> None
  | Some cache_file ->
    match load_checked_file file_name cache_file with
    | _, Inl msg  -> None
    | _, Inr data -> Some data
  )

let load_module_from_cache_internal =
  //this is only used for supressing more than one cache invalid warnings
  let already_failed = mk_ref false in
  fun (try_load:bool) deps fn -> Errors.with_ctx ("While loading module from file " ^ fn) (fun () ->
    let load_it fn () =
      let cache_file = Dep.cache_file_name fn in
      let fail msg cache_file =
        //Don't feel too bad if fn is the file on the command line
        //Also suppress the warning if already given to avoid a deluge
        let suppress_warning = try_load || Options.should_check (Dep.module_name_of_file fn) || !already_failed in
        if not suppress_warning || !dbg then begin
          already_failed := true;
          FStarC.Errors.log_issue (Range.mk_range fn (Range.mk_pos 0 0) (Range.mk_pos 0 0))
            Errors.Warning_CachedFile [Errors.text (Format.fmt3
               "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
               cache_file msg fn)
          ]
        end
      in
      match load_checked_file_with_tc_result
              deps
              fn
              cache_file with
      | Inl msg -> fail msg cache_file; None
      | Inr tc_result ->
        debug (fun _ ->
          Format.print1 "Successfully loaded module from checked file %s\n" cache_file);
        Some tc_result
      (* | _ -> failwith "load_checked_file_tc_result must have an Invalid or Valid entry" *)
    in

    (*
     * AR: cf. #1919, A.fst.checked implicitly depends on A.fsti.checked
     *       and thus, transitively on the dependencies of A.fsti.checked
     *     the dependency on A.fsti.checked is unusual in the sense that
     *       tcenv is not populated with its contents
     *     that happens via interleaving later
     *     this is just to make sure that we correctly track the dependence of A.fst
     *       on the dependences of A.fsti
     *)

    let load_with_profiling fn = Profiling.profile
      (load_it fn)
      None
      "FStarC.CheckedFiles" in

    let i_fn_opt = Dep.interface_of
      deps
      (Dep.lowercase_module_name fn) in

    if Dep.is_implementation fn
    && (i_fn_opt |> Some?)
    then let i_fn = i_fn_opt |> Option.must in
         let i_tc = load_with_profiling i_fn in
         match i_tc with
         | None -> None
         | Some _ -> load_with_profiling fn
           
    else load_with_profiling fn
  )

//This functions checks if the checked file for fn exists
//and if so, whether all its dependences are also checked
//and the hashes are all valid.
//It is used in fly_deps mode when starting up the batch mode
//compiler---if the checked files are all valid, no need to
//check anything again, just load them and go.
let scan_deps_and_check_cache_validity fn : ML (option (list string & Dep.deps)) =
  Dep.with_fly_deps_disabled fun _ ->
  //do it with fly deps disabled so that we compute the full dep graph at once
  let checked_fn = Dep.cache_file_name fn in
  match Find.find_file checked_fn with
  | None -> None //checked files does not exists
  | Some checked_fn ->
    let filenames, dep_graph = 
      FStarC.Parser.Dep.with_fly_deps_disabled
        (fun _ ->
          FStarC.Dependencies.find_deps_if_needed [fn] load_parsing_data_from_cache)
    in
    let rec try_load_all fns : ML (option (list string & Dep.deps)) =
      match fns with
      | [] ->
        Some (filenames, dep_graph)
      | fn::rest ->
        match load_module_from_cache_internal false dep_graph fn with
        | None -> None
        | Some tcres -> try_load_all rest
    in
    try_load_all filenames
 
let load_module_from_cache env fn : ML (option tc_result) =
  load_module_from_cache_internal false (TcEnv.dep_graph env) fn
(*
 * Just to make sure data has the right type
 *)
let store_values_to_cache
    (cache_file:string)
    (stage1:checked_file_entry_stage1)
    (stage2:checked_file_entry_stage2)
    (smt_decls:decls_t)
    :ML string =
  Errors.with_ctx ("While writing checked file " ^ cache_file) (fun () ->
    BU.save_3values_to_file cache_file stage1 stage2 smt_decls)

instance _ : showable Dep.parsing_data = {
  show = Dep.str_of_parsing_data
}

let store_module_to_cache env fn parsing_data_and_direct_deps tc_result : ML unit =
  if Options.cache_checked_modules()
  && not (Options.cache_off())
  then begin
    debug (fun () -> 
      Format.print2 "Storing checked file for %s with %s dependences\n"
        fn (show parsing_data_and_direct_deps)
    );
    if Dep.fly_deps_enabled () then (
      //populate the cache with the interface file, if it exists
      //otherwise dependence hashing will fail
      let i_fn_opt = Dep.interface_of
          (TcEnv.dep_graph env)
          (Dep.lowercase_module_name fn) in
      match i_fn_opt with
      | None -> ()
      | Some iface ->
        debug (fun () -> 
          Format.print1 "Tryng to load interface %s from cache before storing\n"
            iface
        );

        ignore <| load_module_from_cache_internal true (TcEnv.dep_graph env) iface
    );
    let cache_file =
      match Options.output_to () with
      | Some fn -> fn
      (* Note: ^ in this case, main guarantees we were called on a single file, or
         we would clobber previously-written checked files. *)
      | None -> FStarC.Parser.Dep.cache_file_name fn
    in
    (* Never overwrite a checked file that is already there and valid. A module
       can have more than one valid encoding of its checked file: checking
       [M.fst] reveals the implementations of the modules it befriends, so the
       sigelts recorded for [M.fsti] then point at those implementations rather
       than at their interfaces, even though the dependence hashes are the same.
       Rewriting a valid [M.fsti.checked] as a side effect of the [M.fst] job
       silently invalidates every module that was already checked against the
       file we are about to clobber. See #4399. *)
    let already_valid =
      None? (Options.output_to ())
      && not (Options.force ())
      && (match try_find_in_cache cache_file with
          | Some (Valid _, _) -> true
          | _ -> false)
    in
    if already_valid then
      debug (fun () ->
        Format.print1 "Not rewriting checked file %s: it is already present and valid\n"
          cache_file)
    else
    let parsing_data, deps_of_fn = parsing_data_and_direct_deps in
    let digest = hash_dependences (TcEnv.dep_graph env) fn deps_of_fn in
    match digest with
    | Inr hashes ->
      let stage1 = {version=cache_version_number; digest=(BU.digest_of_file fn); parsing_data=parsing_data} in
      let stored = {stored_checked_module=tc_result.checked_module;
                    stored_mii=tc_result.mii;
                    stored_smt_index=tc_result.smt_encoding.me_index;
                    stored_smt_fvbs=tc_result.smt_encoding.me_fvbs} in
      let stage2 = {deps_dig=hashes; tc_res=stored} in
      let checked_digest = store_values_to_cache cache_file stage1 stage2 (tc_result.smt_encoding.me_decls ()) in
      (* Record the digest we just wrote, so that dependents of this module can
         use it without having to read the file back. *)
      ignore <| add_and_return cache_file (Valid checked_digest, Inr parsing_data)
    | Inl msg ->
      let open FStarC.Errors in
      let open FStarC.Errors.Msg in
      let open FStarC.Pprint in
      debug (fun _ ->
          Format.print2 "FAILING to store cache file for %s, with deps %s\n"
            fn (show deps_of_fn));

      log_issue (FStarC.Range.mk_range fn (FStarC.Range.mk_pos 0 0)
                                 (FStarC.Range.mk_pos 0 0))
        Errors.Warning_FileNotWritten [
          text <| Format.fmt1 "Checked file %s was not written." cache_file;
          prefix 2 1 (doc_of_string "Reason:") (text msg)
      ]
  end

let unsafe_raw_load_checked_file (checked_fn:string) : ML (option (FStarC.Parser.Dep.parsing_data & list string & tc_result))
  = let entry : option (string & checked_file_entry_stage1 & checked_file_entry_stage2) =
      BU.load_2values_from_file3 checked_fn
    in
    match entry with
     | Some ((_,s1,s2)) ->
       Some (s1.parsing_data, List.map fst s2.deps_dig, tc_result_of_stored checked_fn s2.tc_res)
     | _ -> None

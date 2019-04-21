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
#light "off"

module FStar.CheckedFiles
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Errors
open FStar.Util
open FStar.Getopt
open FStar.Syntax.Syntax
open FStar.Extraction.ML.UEnv
open FStar.TypeChecker.Env
open FStar.Syntax.DsEnv

(* Module abbreviations for the universal type-checker  *)
module Syntax  = FStar.Syntax.Syntax
module TcEnv   = FStar.TypeChecker.Env
module SMT     = FStar.SMTEncoding.Solver
module BU      = FStar.Util
module Dep     = FStar.Parser.Dep


(*
 * We write this version number to the cache files, and
 * detect when loading the cache that the version number is same
 *)
let cache_version_number = 10

type tc_result = {
  checked_module: Syntax.modul; //persisted
  mii:module_inclusion_info; //persisted
  smt_decls:(FStar.SMTEncoding.Term.decls_t *  //list of smt decls and fvbs for the module
             list<FStar.SMTEncoding.Env.fvar_binding>); //persisted

  tc_time:int;
  extraction_time:int
}

(*
 * Abbreviation for what we store in the checked files
 *)
type checked_file_entry =
  int *                      //cache version number
  
  list<(string * string)> *  //list of (file_name * digest) of direct dependences
                             //file_name is name of the source file and
                             //digest is that of the corresponding checked file
                             //except when the entries are for the current .fst and .fsti,
                             //digest is that of the source file
  
  string *                   //digest of this source file
                             //also present in the list above, but handy to have it here
                             //when checking if parsing data is valid
  
  Parser.Dep.parsing_data *  //parsing data for this file
  
  tc_result                  //typechecking result, including the smt encoding

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
  | Unknown
  | Invalid of string  //reason why this is invalid
  | Valid   of string  //digest of the checked file

(*
 * The cache of checked files
 *)
type cache_t =
  tc_result_t *  //tc data part

  //either: reason why this checked file is not valid for parsing data
  //or    : parsing_data
  either<string, Dep.parsing_data>

//Internal cache
let mcache : smap<cache_t> = BU.smap_create 50

(*
 * Either the reason because of which dependences are stale/invalid
 *   or the list of dep string, as defined in the checked_file_entry above
 *)
let hash_dependences (deps:Dep.deps) (fn:string) :either<string, list<(string * string)>> =
  let fn =
    match FStar.Options.find_file fn with
    | Some fn -> fn
    | _ -> fn
  in
  let module_name = Dep.lowercase_module_name fn in
  let source_hash = BU.digest_of_file fn in
  let has_interface = Option.isSome (Dep.interface_of deps module_name) in
  let interface_hash =
    if Dep.is_implementation fn
    && has_interface
    then ["interface", BU.digest_of_file (Option.get (Dep.interface_of deps module_name))]
    else []
  in
  let binary_deps = Dep.deps_of deps fn
    |> List.filter (fun fn ->
         not (Dep.is_interface fn &&
              Dep.lowercase_module_name fn = module_name)) in
  let binary_deps =
    FStar.List.sortWith
      (fun fn1 fn2 ->
       String.compare (Dep.lowercase_module_name fn1)
                      (Dep.lowercase_module_name fn2))
    binary_deps in
  let rec hash_deps out = function
  | [] -> Inr (("source", source_hash)::interface_hash@out)
  | fn::deps ->
    let cache_fn = Dep.cache_file_name fn in
    (*
     * It is crucial to get the digest of fn from mcache, rather than computing it directly
     * See #1668
     *)
    let digest =
      match BU.smap_try_find mcache cache_fn with
      | None ->
        let msg = BU.format2 "For dependency %s, cache file %s is not loaded" fn cache_fn in
        if Options.debug_any ()
        then BU.print1 "%s\m" msg;
        Inl msg
      | Some (Invalid msg, _) -> Inl msg
      | Some (Valid dig, _)   -> Inr dig
      | Some (Unknown, _)     ->
        failwith (BU.format2
                    "Impossible: unknown entry in the cache for dependence %s of module %s"
                    fn module_name)
    in
    match digest with
    | Inl msg -> Inl msg
    | Inr dig ->
      hash_deps ((Dep.lowercase_module_name fn, dig) :: out) deps
  in
  hash_deps [] binary_deps

(*
 * Load a checked file into mcache
 *
 * This is loading the parsing data, and tc data as Unknown (unless checked file is invalid)
 *
 * See above for the two steps of loading the checked files
 *)
let load_checked_file (fn:string) (checked_fn:string) :cache_t =
  let elt = checked_fn |> BU.smap_try_find mcache in
  if elt |> is_some then elt |> must  //already loaded
  else
    let add_and_return elt = BU.smap_add mcache checked_fn elt; elt in
    if not (BU.file_exists checked_fn)
    then let msg = BU.format1 "checked file %s does not exist" checked_fn in
         add_and_return (Invalid msg, Inl msg)
    else let entry :option<checked_file_entry> = BU.load_value_from_file checked_fn in
         match entry with
         | None ->
           let msg = BU.format1 "checked file %s is corrupt" checked_fn in
           add_and_return (Invalid msg, Inl msg)
         | Some (vnum, _, dig, parsing_data, _) ->
           if vnum <> cache_version_number
           then let msg = BU.format1 "checked file %s has incorrect version" checked_fn in
                add_and_return (Invalid msg, Inl msg)
           else let current_dig = BU.digest_of_file fn in
                if dig <> current_dig
                then begin
                  if Options.debug_any () then
                  BU.print4 "Checked file %s is stale since incorrect digest of %s, \
                    expected: %s, found: %s\n"
                    checked_fn fn current_dig dig;
                  let msg = BU.format2 "checked file %s is stale (digest mismatch for %s)" checked_fn fn in
                  add_and_return (Invalid msg, Inl msg)
                end
                else add_and_return (Unknown, Inr parsing_data)

(*
 * Second step for loading checked files, validates the tc data
 * Either the reason why tc_result is invalid
 *   or tc_result
 *)
let load_checked_file_with_tc_result (deps:Dep.deps) (fn:string) (checked_fn:string)
  :either<string, tc_result> =

  let load_tc_result (fn:string) :list<(string * string)> * tc_result =
    let entry :option<checked_file_entry> = BU.load_value_from_file checked_fn in
    match entry with
     | Some (_, deps_dig, _, _, tc_result) -> deps_dig, tc_result
     | _ ->
       failwith "Impossible! if first phase of loading was unknown, it should have succeeded"
  in

  let elt = load_checked_file fn checked_fn in  //first step, in case some client calls it directly
  match elt with
  | Invalid msg, _ -> Inl msg
  | Valid _, _ -> checked_fn |> load_tc_result |> snd |> Inr
  | Unknown, parsing_data ->
    match hash_dependences deps fn with
    | Inl msg ->
      let elt = (Invalid msg, parsing_data) in
      BU.smap_add mcache checked_fn elt;
      Inl msg
    | Inr deps_dig' ->
      let deps_dig, tc_result = checked_fn |> load_tc_result in
      if deps_dig = deps_dig'
      then begin
        //mark the tc data of the file as valid
        let elt = (Valid (BU.digest_of_file checked_fn), parsing_data) in 
        BU.smap_add mcache checked_fn elt;
        (*
         * if there exists an interface for it, mark that too as valid
         * this is specially needed for extraction invocations of F* with --cmi flag
         * for example, consider a scenario:
         * A.fst -> B.fsti -> prims.fst
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
              match BU.smap_try_find mcache iface_checked_fn with
              | Some (Unknown, parsing_data) ->
                BU.smap_add mcache
                  iface_checked_fn
                  (Valid (BU.digest_of_file iface_checked_fn), parsing_data)
              | _ -> ()
            with
              | _ -> ()
        in
        validate_iface_cache ();
        Inr tc_result
      end
      else begin
        if Options.debug_any()
        then begin
          BU.print4 "Expected (%s) hashes:\n%s\n\nGot (%s) hashes:\n\t%s\n"
            (BU.string_of_int (List.length deps_dig'))
            (FStar.Parser.Dep.print_digest deps_dig')
            (BU.string_of_int (List.length deps_dig))
            (FStar.Parser.Dep.print_digest deps_dig);
          if List.length deps_dig = List.length deps_dig'
          then List.iter2 (fun (x,y) (x', y') ->
                 if x<>x' || y<>y'
                 then BU.print2 "Differ at: Expected %s\n Got %s\n"
                                (FStar.Parser.Dep.print_digest [(x,y)])
                                (FStar.Parser.Dep.print_digest [(x',y')])) deps_dig deps_dig'
        end;
        let msg =
          BU.format1
            "checked file %s is stale (dependence hash mismatch, use --debug yes for more details)"
            checked_fn
        in
        let elt = (Invalid msg, Inl msg) in
        BU.smap_add mcache checked_fn elt;
        Inl msg
      end


let load_parsing_data_from_cache file_name =
  (*
   * the code below suppresses the already_cached assertion failure
   * following is the reason for it:
   *
   * consider a scenario:
   * A.fst -> B.fsti -> prims.fst
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

let load_module_from_cache =
  //this is only used for supressing more than one cache invalid warnings
  let already_failed = BU.mk_ref false in
  fun env fn ->
    let load_it () =
      let cache_file = Dep.cache_file_name fn in
      let fail msg cache_file =
        //Don't feel too bad if fn is the file on the command line
        //Also suppress the warning if already given to avoid a deluge
        let suppress_warning = Options.should_verify_file fn || !already_failed in
        if not suppress_warning then begin
          already_failed := true;
          FStar.Errors.log_issue
            (Range.mk_range fn (Range.mk_pos 0 0) (Range.mk_pos 0 0))
            (Errors.Warning_CachedFile,
             BU.format3
               "Unable to load %s since %s; will recheck %s (suppressing this warning for further modules)"
               cache_file msg fn)
        end
      in
      match load_checked_file_with_tc_result
              (TcEnv.dep_graph env.env_tcenv)
              fn
              cache_file with
      | Inl msg -> fail msg cache_file; None
      | Inr tc_result ->
        if Options.debug_any () then
        BU.print1 "Successfully loaded module from checked file %s\n" cache_file;
        Some tc_result
      | _ -> failwith "load_checked_file_tc_result must have an Invalid or Valid entry"
    in
    Options.profile load_it (fun res ->
      let msg =
        if Option.isSome res
        then "ok"
        else "failed"
      in
      BU.format2 "Loading checked file %s ... %s"
                 (Dep.cache_file_name fn)
                 msg)


(*
 * Just to make sure data has the right type
 *)
let store_value_to_cache (cache_file:string) (data:checked_file_entry) :unit =
  BU.save_value_to_file cache_file data

let store_module_to_cache env fn parsing_data tc_result =
  if Options.cache_checked_modules()
  && not (Options.cache_off())
  then begin
    let cache_file = FStar.Parser.Dep.cache_file_name fn in
    let digest = hash_dependences (TcEnv.dep_graph env.env_tcenv) fn in
    match digest with
    | Inr hashes ->
      let tc_result = { tc_result with tc_time=0; extraction_time=0 } in
        
      //cache_version_number should always be the first field here
      store_value_to_cache cache_file (cache_version_number,
                                       hashes,
                                       BU.digest_of_file fn,
                                       parsing_data,
                                       tc_result)
    | Inl msg ->
      FStar.Errors.log_issue
        (FStar.Range.mk_range fn (FStar.Range.mk_pos 0 0)
                                 (FStar.Range.mk_pos 0 0))
        (Errors.Warning_FileNotWritten,
         BU.format2 "%s was not written since %s"
                    cache_file msg)
  end

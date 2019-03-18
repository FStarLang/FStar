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
let cache_version_number = 9

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
  list<(string * string)> *  //digest of direct dependencies
  string *                   //digest of just this file
  Parser.Dep.parsing_data *  //parsing data for this file
  tc_result                  //typechecking result, including the smt encoding

(*
 * Local cache for checked files contents
 * Note that a checked file could have valid parsing data but stale tc data
 *)

type tc_result_t =
  | Unknown of (list<(string * string)>) * string * tc_result
  | Invalid of string
  | Valid   of string * tc_result

type cache_t =
  //either : reason why this checked file is not valid for tc data
  //or     : digest of this file, tc_result
  tc_result_t *

  //either: reason why this checked file is not valid for parsing data
  //or    : parsing_data
  either<string, Dep.parsing_data>

let mcache : smap<cache_t> = BU.smap_create 50

(*
 * Get the string for hash of dependences of fn
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
    let digest =
      match BU.smap_try_find mcache cache_fn with
      | None ->
        let msg = BU.format2 "For dependency %n, cache file %s is not loaded" fn cache_fn in
        if Options.debug_any ()
        then BU.print1 "%s\m" msg;
        Inl msg
      | Some (Invalid msg, _) -> Inl msg
      | Some (Valid (dig, _), _) -> Inr dig
      | Some (Unknown _, _) -> failwith "Impossible: unknown entry in the cache for a dependence"
    in
    match digest with
    | Inl msg -> Inl msg
    | Inr dig ->
      hash_deps ((Dep.lowercase_module_name fn, dig) :: out) deps
  in
  hash_deps [] binary_deps

(*
 * Load a checked file into mcache
 *)
let load_checked_file (fn:string) (checked_fn:string) :unit =
  if checked_fn |> BU.smap_try_find mcache |> is_some then ()
  else
    if not (BU.file_exists checked_fn)
    then let msg = BU.format1 "checked file %s does not exist" checked_fn in
         BU.smap_add mcache checked_fn (Invalid msg, Inl msg)
    else match BU.load_value_from_file checked_fn with
         | None ->
           let msg = BU.format1 "checked file %s is corrupt" checked_fn in
           BU.smap_add mcache checked_fn (Invalid msg, Inl msg)
         | Some (vnum, deps_dig, dig, parsing_data, tc_result) ->
           if vnum <> cache_version_number
           then let msg = BU.format1 "checked file %s has incorrect version" checked_fn in
                BU.smap_add mcache checked_fn (Invalid msg, Inl msg)
           else let current_dig = BU.digest_of_file fn in
                if dig <> current_dig
                then begin
                  if Options.debug_any () then
                  BU.print4 "Checked file %s is stale since incorrect digest of %s, \
                    expected: %s, found: %s\n"
                    checked_fn fn current_dig dig;
                  let msg = BU.format2 "checked file %s is stale (digest mismatch for %s)" checked_fn fn in
                  BU.smap_add mcache checked_fn (Invalid msg, Inl msg)
                end
                else BU.smap_add mcache checked_fn (Unknown (deps_dig, dig, tc_result), Inr parsing_data)

let load_checked_file_with_tc_result (deps:Dep.deps) (fn:string) (checked_fn:string) :unit =
  load_checked_file fn checked_fn;
  match BU.smap_try_find mcache checked_fn with
  | None -> failwith "Impossible, load_checked_file must add an entry to mcache"
  | Some (Invalid _, _)
  | Some (Valid _, _) -> ()
  | Some (Unknown (deps_dig, dig, tc_result), parsing_data) ->
    match hash_dependences deps fn with
    | Inl msg ->
      BU.smap_add mcache checked_fn (Invalid msg, parsing_data)
    | Inr deps_dig' ->
      if deps_dig = deps_dig'
      then BU.smap_add mcache checked_fn (Valid (dig, tc_result), parsing_data)
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
        BU.smap_add mcache checked_fn (Invalid msg, Inl msg)
      end


(*
 * Read parsing data from the checked file
 * This function is passed as a callback to Parser.Dep
 *)
let load_parsing_data_from_cache file_name :option<Parser.Dep.parsing_data> =
  let cache_file =  //AR: why are we catching this exception?
    try
     Parser.Dep.cache_file_name file_name |> Some
    with _ -> None
  in
  match cache_file with
  | None -> None
  | Some cache_file ->
    load_checked_file file_name cache_file;
    match BU.smap_try_find mcache cache_file with
    | Some (_, Inl msg)  -> None
    | Some (_, Inr data) -> Some data
    | None -> failwith "Impossible, after load_checked_file, mcache should have an entry"


(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)
let load_module_from_cache
    : uenv
    -> string
    -> option<tc_result> =
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
        load_checked_file_with_tc_result (TcEnv.dep_graph env.env_tcenv) fn cache_file;
        match BU.smap_try_find mcache cache_file with
        | Some (Invalid msg, _) -> fail msg cache_file; None
        | Some (Valid (_, tc_result), _) ->
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

let store_module_to_cache (env:uenv) fn (parsing_data:FStar.Parser.Dep.parsing_data)
                          (tc_result:tc_result) =
    if Options.cache_checked_modules()
    && not (Options.cache_off())
    then begin
      let cache_file = FStar.Parser.Dep.cache_file_name fn in
      let digest =
        hash_dependences
        (TcEnv.dep_graph env.env_tcenv)
        fn
      in
      match digest with
      | Inr hashes ->
        let tc_result = { tc_result with tc_time=0; } in
        
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

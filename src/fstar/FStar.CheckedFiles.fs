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
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Common
open FStar.Dependencies
open FStar.Extraction.ML.UEnv
open FStar.TypeChecker.Env
open FStar.Syntax.DsEnv
open FStar.TypeChecker

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
type cache_t = int *  //cache version number
               list<(string * string)> *  //digest of direct dependencies
               string *  //digest of just this file
               Parser.Dep.parsing_data * //parsing data for this file
               tc_result  //typechecking result, including the smt encoding


(*
 * cache_t object * reason for error, if any
 *)
let load_value_from_cache (cache_file:string) :option<cache_t> * string =
  match BU.load_value_from_file cache_file with
  | None -> None, "Corrupt"
  | Some cache_data ->
    let (vnum, _, _, _, _) = cache_data in
    if vnum <> cache_version_number
    then None, "Stale, because inconsistent cache version"
    else Some cache_data, ""

let store_value_to_cache (cache_file:string) (data:cache_t) :unit =
  BU.save_value_to_file cache_file data

(*
 * Read parsing data from the checked file
 * This function is passed as a callback to Parser.Dep
 *)
let load_parsing_data_from_cache file_name :option<Parser.Dep.parsing_data> =
  let cache_file =
    try
     Parser.Dep.cache_file_name file_name |> Some
    with _ -> None
  in
  if cache_file = None then None
  else match cache_file |> must |> load_value_from_cache with
       | None, _ -> None
       | Some (_, _, dig, pd, _), _ ->
         if dig <> BU.digest_of_file file_name then None else Some pd

(***********************************************************************)
(* Loading and storing cache files                                     *)
(***********************************************************************)
let load_module_from_cache
    : uenv
    -> string
    -> option<tc_result> =
    let some_cache_invalid = BU.mk_ref None in
    let invalidate_cache fn = some_cache_invalid := Some fn in
    let load env source_file cache_file =
        match load_value_from_cache cache_file with
        | None, msg ->
            Inl msg
        | Some (_, digest, _, _, tc_result), _ ->
            match FStar.Parser.Dep.hash_dependences
                    (TcEnv.dep_graph env)
                    source_file
                    cache_file
            with
            | Inr digest' ->
                if digest=digest'
                then Inr tc_result
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
            | Inl msg -> Inl msg

    in
    fun env fn ->
      let load_it () =
        let cache_file = Dep.cache_file_name fn in
        let fail msg cache_file =
          invalidate_cache();
          //Don't feel too bad if fn is the file on the command line
          if not (Options.should_verify_file fn) then
            FStar.Errors.log_issue
              (Range.mk_range fn (Range.mk_pos 0 0) (Range.mk_pos 0 0))
              (Errors.Warning_CachedFile,
               BU.format3
                 "Unable to compute digest of %s since %s; will recheck %s and all subsequent files"
                 cache_file msg fn)
        in
        match !some_cache_invalid with
        | Some _ -> None
        | _ ->
          if not (BU.file_exists cache_file) then begin
            fail (BU.format1 "file %s does not exists" cache_file) cache_file;
            None
          end
          else match load env.env_tcenv fn cache_file with
               | Inl msg ->
                 fail msg cache_file;
                 None
               | Inr res -> Some res
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

let store_module_to_cache (env:uenv) fn (parsing_data:FStar.Parser.Dep.parsing_data)
                          (tc_result:tc_result) =
    if Options.cache_checked_modules()
    && not (Options.cache_off())
    then begin
        let cache_file = FStar.Parser.Dep.cache_file_name fn in
        let digest =
          FStar.Parser.Dep.hash_dependences
            (TcEnv.dep_graph env.env_tcenv)
            fn
            cache_file
        in
        match digest with
        | Inr hashes ->
          //cache_version_number should always be the first field here
          let tc_result = {
              tc_result with
                tc_time=0;
          } in
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
             BU.format2 "%s was not written, since some of its dependences were not also checked: %s"
                        cache_file msg)
    end

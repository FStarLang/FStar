(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(** This module provides an ocamldep-like tool for F*, invoked with [fstar --dep].
    Unlike ocamldep, it outputs the transitive closure of the dependency graph
    of a given file. The dependencies that are output are *compilation units*
    (not module names).
*)

#light "off"
module FStar.Parser.Dep

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util

open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Ident

let check_and_strip_suffix f =
  let suffixes = [ ".fsti"; ".fst"; ".fsi"; ".fs" ] in
  let matches = List.map (fun ext ->
    let lext = String.length ext in
    let l = String.length f in
    if l > lext && compare (String.substring f (l - lext) lext) ext = 0 then
      Some (String.substring f 0 (l - lext))
    else
      None
  ) suffixes in
  match List.filter is_some matches with
  | Some m :: _ ->
      Some m
  | _ ->
      None


let is_interface (f: string) =
  String.get f (String.length f - 1) = 'i'

let print_map m =
  List.iter (fun k ->
    Util.fprint2 "%s: %s\n" k (must (smap_try_find m k))
  ) (smap_keys m)

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to filenames (A.B.fst). Long names are all normalized to
    lowercase. *)
let build_map () =
  let include_directories = Options.get_include_path (getcwd ()) in
  let map = smap_create 41 in
  List.iter (fun d ->
    if file_exists d then
      let files = readdir d in
      List.iter (fun f ->
        let f = basename f in
        match check_and_strip_suffix f with
        | Some longname ->
            let key = String.lowercase longname in
            begin match smap_try_find map key with
            | Some existing_file ->
                if String.lowercase existing_file = String.lowercase f then
                  raise (Err (Util.format1 "I'm case insensitive, and I found the same file twice (%s)" f));
                if is_interface existing_file = is_interface f then
                  raise (Err (Util.format1 "Found both a .fs and a .fst (or both a .fsi and a .fsti) (%s)" f));
                (* Note: we always record a dependency against the interface, if found. *)
                if not (is_interface existing_file) then
                  smap_add map key f
            | None ->
                smap_add map key f
            end
        | None ->
            ()
    ) files
  ) include_directories;
  map


(** For all items [i] in the map that start with [prefix], add an additional
    entry where [i] stripped from [prefix] points to the same value. Returns a boolean telling
    whether the map was modified. *)
let enter_namespace original_map working_map prefix =
  let found = ref false in
  let prefix = prefix ^ "." in
  List.iter (fun k ->
    if Util.starts_with k prefix then
      let suffix = String.substring k (String.length prefix) (String.length k - String.length prefix) in
      let filename = must (smap_try_find original_map k) in
      smap_add working_map suffix filename;
      found := true
  ) (smap_keys original_map);
  !found


(** All the components of a [lident] joined by ".".  *)
let lowercase_join_longident (l: lident) (last: bool) =
  let suffix = if last then [ l.ident.idText ] else [ ] in
  let names = List.map (fun x -> x.idText) l.ns @ suffix in
  let names = List.map String.lowercase names in
  String.concat "." names

let check_module_declaration_against_filename (lid: lident) (filename: string) =
  let k' = lowercase_join_longident lid true in
  if compare (must (check_and_strip_suffix (basename filename))) k' <> 0 then
    Util.fprint2 "Warning: the module declaration \"module %s\" found in file %s does not match its filename\n" k' filename

(** Parse a file, walk its AST, return a list of FStar compilation units it
    depends on. *)
let collect_one (original_map: smap<string>) (filename: string) =
  let deps = ref [] in
  let add_dep d =
    deps := d :: !deps
  in
  let working_map = smap_copy original_map in
  let rec collect_fragment = function
    | Inl file ->
        collect_file file
    | Inr decls ->
        collect_decls decls
  and collect_file = function
    | [ modul ] ->
        collect_module modul
    | _ ->
        raise (Err (Util.format1 "File %s does not respect the one module per file convention" filename))
  and collect_module = function
    | Module (lid, decls)
    | Interface (lid, decls, _) ->
        check_module_declaration_against_filename lid filename;
        collect_decls decls
  and collect_decls decls =
    List.iter (fun x -> collect_decl x.d) decls
  and collect_decl = function
    | Open lid ->
        let key = lowercase_join_longident lid true in
        begin match smap_try_find original_map key with
        | Some filename ->
            add_dep filename
        | None ->
            let r = enter_namespace original_map working_map key in
            if not r then
              Util.fprint1 "Warning: no modules in namespace %s\n" key
        end
    | _ ->
        ()
  in
  let ast = Driver.parse_file_raw filename in
  collect_file ast;
  !deps


(** Collect the dependencies for a list of given files. *)
let collect (filenames: list<string>): list<(string * list<string>)> =
  let m = build_map () in
  List.map (fun f ->
    let deps = collect_one m f in
    f, deps
  ) filenames


(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format. *)
let print deps =
  List.iter (fun (f, deps) ->
    let deps = List.map (fun s -> replace_string s " " "\\ ") deps in
    Util.fprint2 "%s: %s\n" f (String.concat " " deps)
  ) deps

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

type map = smap<string>

let check_and_strip_suffix (f: string): option<string> =
  let suffixes = [ ".fsti"; ".fst"; ".fsi"; ".fs" ] in
  let matches = List.map (fun ext ->
    let lext = String.length ext in
    let l = String.length f in
    if l > lext && String.substring f (l - lext) lext = ext then
      Some (String.substring f 0 (l - lext))
    else
      None
  ) suffixes in
  match List.filter is_some matches with
  | Some m :: _ ->
      Some m
  | _ ->
      None


let is_interface (f: string): bool =
  String.get f (String.length f - 1) = 'i'

let print_map (m: map): unit =
  List.iter (fun k ->
    Util.print2 "%s: %s\n" k (must (smap_try_find m k))
  ) (List.unique (smap_keys m))


let lowercase_module_name f =
  match check_and_strip_suffix (basename f) with
  | Some longname ->
      String.lowercase longname
  | None ->
      raise (Err (Util.format1 "not a valid FStar file: %s\n" f))

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to filenames (/path/to/A.B.fst). Long names are all
    normalized to lowercase. *)
let build_map (filenames: list<string>): map =
  let include_directories = Options.get_include_path () in
  let include_directories = List.map normalize_file_path include_directories in
  let include_directories = List.unique include_directories in
  let cwd = normalize_file_path (getcwd ()) in
  let map = smap_create 41 in
  List.iter (fun d ->
    if file_exists d then
      let files = readdir d in
      List.iter (fun f ->
        let f = basename f in
        match check_and_strip_suffix f with
        | Some longname ->
            let key = String.lowercase longname in
            let full_path = if d = cwd then f else join_paths d f in
            begin match smap_try_find map key with
            | Some existing_file ->
                (* The precedence is determined by the order of the --include
                 * arguments passed on the command-line. If at least an
                 * interface exists, we generate a dependency on the interface
                 * with the highest precedence. If no interface exists, we
                 * generate a dependency on the implementation with the highest
                 * precedence. *)
                if not (is_interface existing_file) || is_interface f then
                  smap_add map key full_path
            | None ->
                smap_add map key full_path
            end
        | None ->
            ()
      ) files
    else
      raise (Err (Util.format1 "not a valid include directory: %s\n" d))
  ) include_directories;
  (* All the files we've been given on the command-line must be valid FStar files. *)
  List.iter (fun f ->
    smap_add map (lowercase_module_name f) f
  ) filenames;
  map


(** For all items [i] in the map that start with [prefix], add an additional
    entry where [i] stripped from [prefix] points to the same value. Returns a
    boolean telling whether the map was modified. *)
let enter_namespace (original_map: map) (working_map: map) (prefix: string): bool =
  let found = ref false in
  let prefix = prefix ^ "." in
  List.iter (fun k ->
    if Util.starts_with k prefix then
      let suffix =
        String.substring k (String.length prefix) (String.length k - String.length prefix)
      in
      let filename = must (smap_try_find original_map k) in
      smap_add working_map suffix filename;
      found := true
  ) (List.unique (smap_keys original_map));
  !found


let string_of_lid (l: lident) (last: bool) =
  let suffix = if last then [ l.ident.idText ] else [ ] in
  let names = List.map (fun x -> x.idText) l.ns @ suffix in
  String.concat "." names


(** All the components of a [lident] joined by "." (the last component of the
 * lident is included iff [last = true]).  *)
let lowercase_join_longident (l: lident) (last: bool) =
  String.lowercase (string_of_lid l last)


let check_module_declaration_against_filename (lid: lident) (filename: string): unit =
  let k' = lowercase_join_longident lid true in
  if String.lowercase (must (check_and_strip_suffix (basename filename))) <> k' then
    Util.fprint stderr "Warning: the module declaration \"module %s\" \
      found in file %s does not match its filename. Dependencies will be \
      incorrect.\n" [string_of_lid lid true; filename]

exception Exit

(** Parse a file, walk its AST, return a list of FStar lowercased module names
    it depends on. *)
let collect_one (original_map: smap<string>) (filename: string): list<string> =
  let deps = ref [] in
  let add_dep d =
    if not (List.existsb (fun d' -> d' = d) !deps) then
      deps := d :: !deps
  in
  let working_map = smap_copy original_map in

  let record_open lid =
    let key = lowercase_join_longident lid true in
    begin match smap_try_find original_map key with
    | Some filename ->
        add_dep (lowercase_module_name filename)
    | None ->
        let r = enter_namespace original_map working_map key in
        if not r then
          Util.fprint stderr "Warning: no modules in namespace %s and no file with \
            that name either\n" [string_of_lid lid true]
    end
  in
  let record_module_alias ident lid =
    let key = String.lowercase (text_of_id ident) in
    let alias = lowercase_join_longident lid true in
    let deps_of_aliased_module = must (smap_try_find working_map alias) in
    smap_add working_map key deps_of_aliased_module
  in

  (* In [dsenv.fs], in [prepare_module_or_interface], some open directives are
   * auto-generated. *)
  let auto_open =
    let index_of s l =
      let found = ref (-1) in
      try
        List.iteri (fun i x ->
          if s = x then begin
            found := i;
            raise Exit
          end
        ) l;
        -1
      with Exit ->
        !found
    in
    (* All the dependencies of FStar.All.fst, in order. *)
    let ordered = [
      "fstar"; "prims"; "fstar.list.tot"; "fstar.functionalextensionality";
      "fstar.set"; "fstar.heap"; "fstar.map"; "fstar.hyperheap"; "fstar.st"; "fstar.all"
    ] in
    (* The [open] statements that we wish to prepend. *)
    let desired_opens = [ Const.fstar_ns_lid; Const.prims_lid; Const.st_lid; Const.all_lid ] in
    let me = String.lowercase (must (check_and_strip_suffix (basename filename))) in
    let index_or_length s l =
      let i = index_of s l in
      if i < 0 then List.length l else i
    in
    let my_index = index_or_length me ordered in
    List.filter (fun lid -> index_or_length (lowercase_join_longident lid true) ordered < my_index) desired_opens
  in
  List.iter record_open auto_open;

  let rec collect_fragment = function
    | Inl file ->
        collect_file file
    | Inr decls ->
        collect_decls decls

  and collect_file = function
    | [ modul ] ->
        collect_module modul
    | modules ->
        Util.fprint stderr "Warning: file %s does not respect the one module per file convention\n" [ filename ];
        List.iter collect_module modules

  and collect_module = function
    | Module (lid, decls)
    | Interface (lid, decls, _) ->
        check_module_declaration_against_filename lid filename;
        collect_decls decls

  and collect_decls decls =
    List.iter (fun x -> collect_decl x.d) decls

  and collect_decl = function
    | Open lid ->
        record_open lid
    | ModuleAbbrev (ident, lid) ->
        record_module_alias ident lid
    | ToplevelLet (_, _, patterms) ->
        List.iter (fun (_, t) -> collect_term t) patterms
    | KindAbbrev (_, binders, t) ->
        collect_term t;
        collect_binders binders
    | Main t
    | Assume (_, _, t)
    | SubEffect { lift_op = t }
    | Val (_, _, t) ->
        collect_term t
    | Tycon (_, ts) ->
        List.iter collect_tycon ts
    | Exception (_, t) ->
        iter_opt t collect_term
    | NewEffect (_, ed) ->
        collect_effect_decl ed
    | Pragma _ ->
        ()

  and collect_tycon = function
    | TyconAbstract (_, binders, k) ->
        collect_binders binders;
        iter_opt k collect_term
    | TyconAbbrev (_, binders, k, t) ->
        collect_binders binders;
        iter_opt k collect_term;
        collect_term t
    | TyconRecord (_, binders, k, identterms) ->
        collect_binders binders;
        iter_opt k collect_term;
        List.iter (fun (_, t) -> collect_term t) identterms
    | TyconVariant (_, binders, k, identterms) ->
        collect_binders binders;
        iter_opt k collect_term;
        List.iter (fun (_, t, _) -> iter_opt t collect_term) identterms

  and collect_effect_decl = function
    | DefineEffect (_, binders, t, decls) ->
        collect_binders binders;
        collect_term t;
        collect_decls decls
    | RedefineEffect (_, binders, t) ->
        collect_binders binders;
        collect_term t

  and collect_binders binders =
    List.iter collect_binder binders

  and collect_binder = function
    | { b = Annotated (_, t) }
    | { b = TAnnotated (_, t) } ->
        collect_term t
    | _ ->
        ()

  and collect_term t =
    collect_term' t.tm

  and collect_term' = function
    | Wild ->
        ()
    | Const _ ->
        ()
    | Op (_, ts) ->
        List.iter collect_term ts
    | Tvar _ ->
        ()
    | Var lid
    | Name lid ->
        (* XXX this is where stuff happens *)
        let key = lowercase_join_longident lid false in
        begin match smap_try_find working_map key with
        | Some filename ->
            add_dep (lowercase_module_name filename)
        | None ->
            if List.length lid.ns > 0 && !Options.debug <> [] then
              Util.fprint stderr "Warning: unbound module reference %s\n" [string_of_lid lid false]
        end

    | Construct (_, termimps) ->
        List.iter (fun (t, _) -> collect_term t) termimps
    | Abs (pats, t) ->
        collect_patterns pats;
        collect_term t
    | App (t1, t2, _) ->
        collect_term t1;
        collect_term t2
    | Let (_, patterms, t) ->
        List.iter (fun (_, t) -> collect_term t) patterms;
        collect_term t
    | Seq (t1, t2) ->
        collect_term t1;
        collect_term t2
    | If (t1, t2, t3) ->
        collect_term t1;
        collect_term t2;
        collect_term t3
    | Match (t, bs)
    | TryWith (t, bs) ->
        collect_term t;
        collect_branches bs
    | Ascribed (t1, t2) ->
        collect_term t1;
        collect_term t2
    | Record (t, idterms) ->
        iter_opt t collect_term
    | Project (t, _) ->
        collect_term t
    | Product (binders, t)
    | Sum (binders, t) ->
        collect_binders binders;
        collect_term t
    | QForall (binders, ts, t)
    | QExists (binders, ts, t) ->
        collect_binders binders;
        List.iter (List.iter collect_term) ts;
        collect_term t
    | Refine (binder, t) ->
        collect_binder binder;
        collect_term t
    | NamedTyp (_, t) ->
        collect_term t
    | Paren t ->
        collect_term t
    | Requires (t, _)
    | Ensures (t, _)
    | Labeled (t, _, _) ->
        collect_term t

  and collect_patterns ps =
    List.iter collect_pattern ps

  and collect_pattern p =
    collect_pattern' p.pat

  and collect_pattern' = function
    | PatWild ->
        ()
    | PatConst _ ->
        ()
    | PatApp (p, ps) ->
        collect_pattern p;
        collect_patterns ps
    | PatVar _
    | PatName _
    | PatTvar _ ->
        ()
    | PatList ps
    | PatOr ps
    | PatTuple (ps, _) ->
        collect_patterns ps
    | PatRecord lidpats ->
        List.iter (fun (_, p) -> collect_pattern p) lidpats
    | PatAscribed (p, t) ->
        collect_pattern p;
        collect_term t


  and collect_branches bs =
    List.iter collect_branch bs

  and collect_branch (pat, t1, t2) =
    collect_pattern pat;
    iter_opt t1 collect_term;
    collect_term t2

  in
  let ast = Driver.parse_file filename in
  collect_file ast;
  !deps

type color = | White | Gray | Black

(** Collect the dependencies for a list of given files. *)
let collect (filenames: list<string>): _ =
  (* The dependency graph; keys are lowercased module names, values = list of
   * lowercased module names this file depends on. *)
  let graph = smap_create 41 in

  (* A map from lowercase module names (e.g. [a.b.c]) to the corresponding
   * filenames (e.g. [/where/to/find/A.B.C.fst]). Consider this map
   * immutable from there on. *)
  let m = build_map filenames in

  (* This function takes a lowercase module name. *)
  let rec discover_one key =
    if smap_try_find graph key = None then
      let filename = must (smap_try_find m key) in
      let deps = collect_one m filename in
      smap_add graph key (deps, White);
      List.iter discover_one deps
  in
  List.iter discover_one (List.map lowercase_module_name filenames);

  (* At this point, we have the (immediate) dependency graph of all the files. *)
  let print_graph () =
    List.iter (fun k ->
      Util.print2 "%s: %s\n" k (String.concat " " (fst (must (smap_try_find graph k))))
    ) (List.unique (smap_keys graph))
  in

  let topologically_sorted = ref [] in

  (* Compute the transitive closure. *)
  let rec discover key =
    let direct_deps, color = must (smap_try_find graph key) in
    match color with
    | Gray ->
        Util.print1 "Warning: recursive dependency on module %s\n" key;
        print_string "Here's the (non-transitive) dependency graph:\n";
        print_graph ();
        print_string "\n";
        exit 1
    | Black ->
        (* If the element has been visited already, then the map contains all its
         * dependencies. Otherwise, the map only contains its direct dependencies. *)
        direct_deps
    | White ->
        (* Unvisited. Compute. *)
        smap_add graph key (direct_deps, Gray);
        let all_deps = List.unique (List.flatten (List.map (fun dep ->
          dep :: discover dep
        ) direct_deps)) in
        (* Mutate the graph (it now remembers transitive dependencies). *)
        smap_add graph key (all_deps, Black);
        (* Also build the topological sort (Tarjan's algorithm). *)
        topologically_sorted := key :: !topologically_sorted;
        (* Returns transitive dependencies *)
        all_deps
  in

  let must_find k =
    must (smap_try_find m k)
  in
  let by_target = List.map (fun k ->
    let deps = List.rev (discover k) in
    must_find k, List.map must_find deps
  ) (smap_keys graph) in
  let topologically_sorted = List.map must_find !topologically_sorted in

  by_target, topologically_sorted


(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format. *)
let print_make (deps: list<(string * list<string>)>): unit =
  List.iter (fun (f, deps) ->
    let deps = List.map (fun s -> replace_string s " " "\\ ") deps in
    Util.print2 "%s: %s\n" f (String.concat " " deps)
  ) deps

let print (deps: _): unit =
  match !Options.dep with
  | Some "make" ->
      print_make (fst deps)
  | Some _ ->
      raise (Err "unknown tool for --dep\n")
  | None ->
      assert false

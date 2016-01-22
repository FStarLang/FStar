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

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to absolute filenames (/path/to/A.B.fst). Long names are all
    normalized to lowercase. *)
let build_map (): map =
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
                  smap_add map key (join_paths d f)
            | None ->
                smap_add map key (join_paths d f)
            end
        | None ->
            ()
    ) files
  ) include_directories;
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


(** All the components of a [lident] joined by ".".  *)
let lowercase_join_longident (l: lident) (last: bool) =
  String.lowercase (string_of_lid l last)


let check_module_declaration_against_filename (lid: lident) (filename: string): unit =
  let k' = lowercase_join_longident lid true in
  if String.lowercase (must (check_and_strip_suffix (basename filename))) <> k' then
    Util.fprint stderr "Warning: the module declaration \"module %s\" \
      found in file %s does not match its filename. Dependencies will be \
      incorrect.\n" [string_of_lid lid true; filename]

exception Exit

(** Parse a file, walk its AST, return a list of FStar compilation units it
    depends on. *)
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
        add_dep filename
    | None ->
        let r = enter_namespace original_map working_map key in
        if not r then
          Util.fprint stderr "Warning: no modules in namespace %s and no file with \
          that name either\n" [string_of_lid lid true]
    end
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
    let ordered = [ "fstar"; "prims"; "fstar.set"; "fstar.heap"; "fstar.st"; "fstar.all" ] in
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
        record_open lid
    | ToplevelLet (_, patterms) ->
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
            add_dep filename
        | None ->
            if List.length lid.ns > 0 then
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
  let ast = Driver.parse_file_raw filename in
  collect_file ast;
  !deps


(** A list of filenames along with the direct dependencies for each file. *)
type t = list<(string * list<string>)>

type color = | White | Gray | Black

(** Collect the dependencies for a list of given files. *)
let collect (filenames: list<string>): t =
  (* The dependency graph; keys are filenames, values = list of filenames this
   * file depends on. *)
  let graph = smap_create 41 in

  (* A map from lowercase paths (e.g. [a.b.c]) to the corresponding filenames
   * (e.g. [A.B.C.fst]). Consider this map immutable from there on. *)
  let m = build_map () in

  (* This works because we check in [build_map] that there are no collisions
   * (i.e. no two files have the same name) in the include path. *)
  let rec discover_one f =
    let short = basename f in
    if smap_try_find graph short = None then
      let deps = collect_one m f in
      smap_add graph short (deps, White);
      List.iter discover_one deps
  in
  List.iter discover_one filenames;

  (* At this point, we have the (immediate) dependency graph of all the files. *)
  let print_graph () =
    List.iter (fun k ->
      Util.print2 "%s: %s\n" k (String.concat " " (fst (must (smap_try_find graph k))))
    ) (List.unique (smap_keys graph))
  in

  (* Compute the transitive closure. *)
  let rec discover f =
    let short = basename f in
    let direct_deps, color = must (smap_try_find graph short) in
    match color with
    | Gray ->
        Util.print1 "Recursive dependency on file %s\n" f;
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
        smap_add graph short (direct_deps, Gray);
        let all_deps = List.unique (List.flatten (List.map (fun dep ->
          dep :: discover dep
        ) direct_deps)) in
        smap_add graph short (all_deps, Black);
        all_deps
  in

  List.map (fun f -> f, List.rev (discover f)) filenames


(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format. *)
let print_make (deps: t): unit =
  List.iter (fun (f, deps) ->
    let deps = List.map (fun s -> replace_string s " " "\\ " |> basename) deps in
    Util.print2 "%s: %s\n" f (String.concat " " deps)
  ) deps

let print_nubuild (deps: t): unit =
  let f, deps = List.hd (List.rev deps) in
  List.iter print_endline deps

let print (deps: t): unit =
  match !Options.dep with
  | Some "nubuild" ->
      print_nubuild deps
  | Some "make" ->
      print_make deps
  | Some _ ->
      failwith "Unknown tool for --dep"
  | None ->
      assert false

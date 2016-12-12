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
#light "off"

(** This module provides an ocamldep-like tool for F*, invoked with [fstar --dep].
    Unlike ocamldep, it outputs the transitive closure of the dependency graph
    of a given file. The dependencies that are output are *compilation units*
    (not module names).
*)
module FStar.Parser.Dep

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Const

open FStar.Absyn
open FStar.Absyn.Syntax
open FStar.Ident

(* In case the user passed [--verify_all], we record every single module name we
 * found in the list of modules to be verified.
 * In the [VerifyUserList] case, for every [--verify_module X], we check we
 * indeed find a module [X].
 * In the [VerifyFigureItOut] case, for every file that was on the command-line,
 * we record its module name as one module to be verified.
 *)
type verify_mode =
  | VerifyAll
  | VerifyUserList
  | VerifyFigureItOut

type map = smap<(option<string> * option<string>)>

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

let is_implementation f =
  not (is_interface f)

let list_of_option = function Some x -> [x] | None -> []

let list_of_pair (intf, impl) =
  list_of_option intf @ list_of_option impl

(* Old behavior: just pick the interface if presented with both the interface
 * and the implementation. *)
let must_find_stratified m k =
  match must (smap_try_find m k) with
  | Some intf, _ ->
      [ intf ]
  | None, Some impl ->
      [ impl ]
  | None, None ->
      []

let must_find_universes m k =
  list_of_pair (must (smap_try_find m k))

let must_find m k =
  if Options.universes () then
    must_find_universes m k
  else
    must_find_stratified m k

let print_map (m: map): unit =
  List.iter (fun k ->
    List.iter (fun f ->
      Util.print2 "%s: %s\n" k f
    ) (must_find m k)
  ) (List.unique (smap_keys m))


let lowercase_module_name f =
  match check_and_strip_suffix (basename f) with
  | Some longname ->
      String.lowercase longname
  | None ->
      raise (Err (Util.format1 "not a valid FStar file: %s\n" f))

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to pairs of filenames (/path/to/A.B.fst). Long names are
    all normalized to lowercase. The first component of the pair is the
    interface (if any). The second component of the pair is the implementation
    (if any). *)
let build_map (filenames: list<string>): map =
  let include_directories = Options.include_path () in
  let include_directories = List.map normalize_file_path include_directories in
  (* Note that [BatList.unique] keeps the last occurrence, that way one can
   * always override the precedence order. *)
  let include_directories = List.unique include_directories in
  let cwd = normalize_file_path (getcwd ()) in
  let map = smap_create 41 in
  let add_entry key full_path =
    match smap_try_find map key with
    | Some (intf, impl) ->
        if is_interface full_path then
          smap_add map key (Some full_path, impl)
        else
          smap_add map key (intf, Some full_path)
    | None ->
        if is_interface full_path then
          smap_add map key (Some full_path, None)
        else
          smap_add map key (None, Some full_path)
  in
  List.iter (fun d ->
    if file_exists d then
      let files = readdir d in
      List.iter (fun f ->
        let f = basename f in
        match check_and_strip_suffix f with
        | Some longname ->
            let full_path = if d = cwd then f else join_paths d f in
            let key = String.lowercase longname in
            add_entry key full_path
        | None ->
            ()
      ) files
    else
      raise (Err (Util.format1 "not a valid include directory: %s\n" d))
  ) include_directories;
  (* All the files we've been given on the command-line must be valid FStar files. *)
  List.iter (fun f ->
    add_entry (lowercase_module_name f) f
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
let collect_one (verify_flags: list<(string * ref<bool>)>) (verify_mode: verify_mode) (is_user_provided_filename: bool) (original_map: map) (filename: string): list<string> =
  let deps = ref [] in
  let add_dep d =
    if not (List.existsb (fun d' -> d' = d) !deps) then
      deps := d :: !deps
  in
  let working_map = smap_copy original_map in

  let record_open let_open lid =
    let key = lowercase_join_longident lid true in
    begin match smap_try_find working_map key with
    | Some pair ->
        List.iter (fun f -> add_dep (lowercase_module_name f)) (list_of_pair pair)
    | None ->
        let r = enter_namespace original_map working_map key in
        if not r then begin
          if let_open then
            raise (Err ("let-open only supported for modules, not namespaces"))
          else
            Util.fprint stderr "Warning: no modules in namespace %s and no file with \
              that name either\n" [string_of_lid lid true]
        end
    end
  in
  let record_module_alias ident lid =
    let key = String.lowercase (text_of_id ident) in
    let alias = lowercase_join_longident lid true in
    // Only fully qualified module aliases are allowed.
    match smap_try_find original_map alias with
    | Some deps_of_aliased_module ->
        smap_add working_map key deps_of_aliased_module
    | None ->
        raise (Err (Util.format1 "module not found in search path: %s\n" alias))
  in
  let record_lid is_constructor lid =
    if lid.ident.idText <> "reflect" then
      let try_key key =
        begin match smap_try_find working_map key with
        | Some pair ->
            List.iter (fun f -> add_dep (lowercase_module_name f)) (list_of_pair pair)
        | None ->
            if List.length lid.ns > 0 && Options.debug_any() then
              Util.fprint stderr "Warning: unbound module reference %s\n" [string_of_lid lid false]
        end
      in
      // Option.Some x
      try_key (lowercase_join_longident lid false);
      // FStar.List (flatten (map (...)))
      if is_constructor then
        try_key (lowercase_join_longident lid true)
  in


  (* In [dsenv.fs], in [prepare_module_or_interface], some open directives are
   * auto-generated. With universes, there's some copy/pasta in [env.fs] too. *)
  let auto_open =
    if basename filename = "prims.fst" then
      []
    else if starts_with (String.lowercase (basename filename)) "fstar." then
      [ Const.fstar_ns_lid; Const.prims_lid ]
    else
      [ Const.fstar_ns_lid; Const.prims_lid; Const.st_lid; Const.all_lid ]
  in
  List.iter (record_open false) auto_open;

  let num_of_toplevelmods = ref 0 in

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
        begin match verify_mode with
        | VerifyAll ->
            Options.add_verify_module (string_of_lid lid true)
        | VerifyFigureItOut ->
            if is_user_provided_filename then
              Options.add_verify_module (string_of_lid lid true)
        | VerifyUserList ->
            List.iter (fun (m, r) ->
              if String.lowercase m = String.lowercase (string_of_lid lid true) then
                r := true
            ) verify_flags
        end;
        collect_decls decls

  and collect_decls decls =
    List.iter (fun x -> collect_decl x.d) decls

  and collect_decl = function
    | Include lid
    | Open lid ->
        record_open false lid
    | ModuleAbbrev (ident, lid) ->
        add_dep (lowercase_join_longident lid true);
        record_module_alias ident lid
    | TopLevelLet (_, _, patterms) ->
        List.iter (fun (pat, t) -> collect_pattern pat; collect_term t) patterms
    | KindAbbrev (_, binders, t) ->
        collect_term t;
        collect_binders binders
    | Main t
    | Assume (_, _, t)
    | SubEffect { lift_op = NonReifiableLift t }
    | SubEffect { lift_op = LiftForFree t }
    | Val (_, _, t) ->
        collect_term t
    | SubEffect { lift_op = ReifiableLift (t0, t1) } ->
        collect_term t0;
        collect_term t1
    | Tycon (_, ts) ->
        let ts = List.map (fun (x,doc) -> x) ts in
        List.iter collect_tycon ts
    | Exception (_, t) ->
        iter_opt t collect_term
    | NewEffectForFree (_, ed)
    | NewEffect (_, ed) ->
        collect_effect_decl ed
    | Fsdoc _
    | Pragma _ ->
        ()
    | TopLevelModule lid ->
        incr num_of_toplevelmods;
        if (!num_of_toplevelmods > 1) then
            raise (Err (Util.format1 "Automatic dependency analysis demands one \
              module per file (module %s not supported)" (string_of_lid lid true)))

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
        List.iter (fun (_, t, _) -> collect_term t) identterms
    | TyconVariant (_, binders, k, identterms) ->
        collect_binders binders;
        iter_opt k collect_term;
        List.iter (fun (_, t, _, _) -> iter_opt t collect_term) identterms

  and collect_effect_decl = function
    | DefineEffect (_, binders, t, decls, actions) ->
        collect_binders binders;
        collect_term t;
        collect_decls decls;
        collect_decls actions
    | RedefineEffect (_, binders, t) ->
        collect_binders binders;
        collect_term t

  and collect_binders binders =
    List.iter collect_binder binders

  and collect_binder = function
    | { b = Annotated (_, t) }
    | { b = TAnnotated (_, t) }
    | { b = NoName t } ->
        collect_term t
    | _ ->
        ()

  and collect_term t =
    collect_term' t.tm

  and collect_constant = function
    | Const_int (_, Some (signedness, width)) ->
        let u = match signedness with | Unsigned -> "u" | Signed -> "" in
        let w = match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64" in
        add_dep (Util.format2 "fstar.%sint%s" u w)
    | _ ->
        ()

  and collect_term' = function
    | Wild ->
        ()
    | Const c ->
        collect_constant c
    | Op (s, ts) ->
        if s = "@" then
          collect_term' (Name (lid_of_path (path_of_text "FStar.List.Tot.append") Range.dummyRange));
        List.iter collect_term ts
    | Tvar _
    | AST.Uvar _ ->
        ()
    | Var lid
    | AST.Projector (lid, _)
    | AST.Discrim lid
    | Name lid ->
        record_lid false lid
    | Construct (lid, termimps) ->
        if List.length termimps = 1 && Options.universes () then
          record_lid true lid;
        List.iter (fun (t, _) -> collect_term t) termimps
    | Abs (pats, t) ->
        collect_patterns pats;
        collect_term t
    | App (t1, t2, _) ->
        collect_term t1;
        collect_term t2
    | Let (_, patterms, t) ->
        List.iter (fun (pat, t) -> collect_pattern pat; collect_term t) patterms;
        collect_term t
    | LetOpen (lid, t) ->
        record_open true lid;
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
        iter_opt t collect_term;
        List.iter (fun (_, t) -> collect_term t) idterms
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
    | Assign (_, t)
    | Requires (t, _)
    | Ensures (t, _)
    | Labeled (t, _, _) ->
        collect_term t
    | Attributes cattributes  ->
        List.iter collect_term cattributes

  and collect_patterns ps =
    List.iter collect_pattern ps

  and collect_pattern p =
    collect_pattern' p.pat

  and collect_pattern' = function
    | PatWild
    | PatOp _
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
  (* Util.print2 "Deps for %s: %s\n" filename (String.concat " " (!deps)); *)
  !deps

type color = | White | Gray | Black

let print_graph graph =
  Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph";
  Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  Util.write_file "dep.graph" (
    "digraph {\n" ^
    String.concat "\n" (List.collect (fun k ->
      let deps = fst (must (smap_try_find graph k)) in
      let r s = replace_char s '.' '_' in
      List.map (fun dep -> Util.format2 "  %s -> %s" (r k) (r dep)) deps
    ) (List.unique (smap_keys graph))) ^
    "\n}\n"
  )

(** Collect the dependencies for a list of given files. *)
let collect (verify_mode: verify_mode) (filenames: list<string>): _ =
  (* The dependency graph; keys are lowercased module names, values = list of
   * lowercased module names this file depends on. *)
  let graph = smap_create 41 in

  (* A bitmap that ensures every --verify_module X was matched by an existing X
   * in our dependency graph. *)
  let verify_flags = List.map (fun f -> f, ref false) (Options.verify_module ()) in

  (* A map from lowercase module names (e.g. [a.b.c]) to the corresponding
   * filenames (e.g. [/where/to/find/A.B.C.fst]). Consider this map
   * immutable from there on. *)
  let m = build_map filenames in
  (* Debug. *)
  (* List.map (fun k ->
    let p = function
      | Some x -> Util.format1 "Some %s" x
      | None -> "None"
    in
    let intf, impl = must (smap_try_find m k) in
    Util.print3 "%s: %s, %s\n" k (p intf) (p impl)
  ) (smap_keys m); *)

  let collect_one = collect_one verify_flags verify_mode in

  (* This function takes a lowercase module name. *)
  let rec discover_one is_user_provided_filename key =
    if smap_try_find graph key = None then
      (* Util.print1 "key: %s\n" key; *)
      let intf, impl = must (smap_try_find m key) in
      let intf_deps =
        match intf with
        | None -> []
        | Some intf -> collect_one is_user_provided_filename m intf
      in
      let impl_deps =
        match impl with
        | None -> []
        | Some impl -> collect_one is_user_provided_filename m impl
      in
      let deps = List.unique (impl_deps @ intf_deps) in
      smap_add graph key (deps, White);
      List.iter (discover_one false) deps
  in
  List.iter (discover_one true) (List.map lowercase_module_name filenames);

  (* At this point, we have the (immediate) dependency graph of all the files. *)
  let immediate_graph = smap_copy graph in

  let topologically_sorted = ref [] in

  (* Compute the transitive closure. *)
  let rec discover cycle key =
    let direct_deps, color = must (smap_try_find graph key) in
    match color with
    | Gray ->
        Util.print1 "Warning: recursive dependency on module %s\n" key;
        Util.print1 "The cycle is: %s \n" (String.concat " -> " cycle);
        print_graph immediate_graph;
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
          dep :: discover (key :: cycle) dep
        ) direct_deps)) in
        (* Mutate the graph (it now remembers transitive dependencies). *)
        smap_add graph key (all_deps, Black);
        (* Also build the topological sort (Tarjan's algorithm). *)
        topologically_sorted := key :: !topologically_sorted;
        (* Returns transitive dependencies *)
        all_deps
  in
  let discover = discover [] in

  let must_find = must_find m in
  let must_find_r f = List.rev (must_find f) in
  let by_target = List.collect (fun k ->
    let as_list = must_find k in
    let is_interleaved = List.length as_list = 2 in
    List.map (fun f ->
      let should_append_fsti = is_implementation f && is_interleaved in
      let suffix = if should_append_fsti then [ f ^ "i" ] else [] in
      let k = lowercase_module_name f in
      let deps = List.rev (discover k) in
      let deps_as_filenames = List.collect must_find deps @ suffix in
      (* List stored in the "right" order. *)
      f, deps_as_filenames
    ) as_list
  ) (smap_keys graph) in
  let topologically_sorted = List.collect must_find_r !topologically_sorted in

  List.iter (fun (m, r) ->
    if not !r && not (Options.interactive ()) then
      raise (Err (Util.format2 "You passed --verify_module %s but I found no \
        file that contains [module %s] in the dependency graph\n" m m))
  ) verify_flags;

  (* At this stage the list is kept in reverse to make sure the caller in
   * [dependencies.fs] can chop [prims.fst] off its head. So make sure we have
   * [fst, fsti] so that, once reversed, it shows up in the correct order. *)
  by_target, topologically_sorted, immediate_graph


(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format. *)
let print_make (deps: list<(string * list<string>)>): unit =
  List.iter (fun (f, deps) ->
    let deps = List.map (fun s -> replace_string s " " "\\ ") deps in
    Util.print2 "%s: %s\n" f (String.concat " " deps)
  ) deps

let print (make_deps, _, graph): unit =
  match (Options.dep()) with
  | Some "make" ->
      print_make make_deps
  | Some "graph" ->
      print_graph graph
  | Some _ ->
      raise (Err "unknown tool for --dep\n")
  | None ->
      assert false

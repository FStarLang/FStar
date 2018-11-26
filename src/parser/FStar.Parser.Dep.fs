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
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Const
open FStar.String
open FStar.Ident
open FStar.Errors

module Const = FStar.Parser.Const
module BU = FStar.Util

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

type files_for_module_name = smap<(option<string> * option<string>)>

type color = | White | Gray | Black

(* In public interface *)
type open_kind = | Open_module | Open_namespace

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

(* In public interface *)
let is_interface (f: string): bool =
  String.get f (String.length f - 1) = 'i'

(* In public interface *)
let is_implementation f =
  not (is_interface f)


let list_of_option = function Some x -> [x] | None -> []

let list_of_pair (intf, impl) =
  list_of_option intf @ list_of_option impl

(* In public interface *)
let module_name_of_file f =
    match check_and_strip_suffix (basename f) with
    | Some longname ->
      longname
    | None ->
      raise_err (Errors.Fatal_NotValidFStarFile, (Util.format1 "not a valid FStar file: %s" f))

(* In public interface *)
let lowercase_module_name f = String.lowercase (module_name_of_file f)

let namespace_of_module f =
    let lid = FStar.Ident.lid_of_path (FStar.Ident.path_of_text f) Range.dummyRange in
    match lid.ns with
    | [] -> None
    | _ -> Some (FStar.Ident.lid_of_ids lid.ns)

type file_name = string
type module_name = string
type dependence =
    | UseInterface of module_name
    | PreferInterface of module_name
    | UseImplementation of module_name
    | FriendImplementation of module_name
let dep_to_string = function
    | UseInterface f -> "UseInterface " ^ f
    | PreferInterface f -> "PreferInterface " ^ f
    | UseImplementation f -> "UseImplementation " ^ f
    | FriendImplementation f -> "FriendImplementation " ^ f
type dependences = list<dependence>
let empty_dependences = []
type dependence_graph = //maps file names to the modules it depends on
     | Deps of smap<(dependences * color)>
type deps = {
    dep_graph:dependence_graph;              //dependences of the entire project, not just those reachable from the command line
    file_system_map:files_for_module_name;   //an abstraction of the file system
    cmd_line_files:list<file_name>;          //all command-line files
    all_files:list<file_name>;               //all files
    interfaces_with_inlining:list<module_name> //interfaces that use `inline_for_extraction` require inlining
}
let deps_try_find (Deps m) k = BU.smap_try_find m k
let deps_add_dep (Deps m) k v =
  BU.smap_add m k v
let deps_keys (Deps m) = BU.smap_keys m
let deps_empty () = Deps (BU.smap_create 41)
let mk_deps dg fs c a i = {
    dep_graph=dg;
    file_system_map=fs;
    cmd_line_files=c;
    all_files=a;
    interfaces_with_inlining=i
}
(* In public interface *)
let empty_deps = mk_deps (deps_empty ()) (BU.smap_create 0) [] [] []
let module_name_of_dep = function
    | UseInterface m
    | PreferInterface m
    | UseImplementation m
    | FriendImplementation m -> m

let resolve_module_name (file_system_map:files_for_module_name) (key:module_name)
    : option<module_name>
    = match BU.smap_try_find file_system_map key with
      | Some (Some fn, _)
      | Some (_, Some fn) -> Some (lowercase_module_name fn)
      | _ -> None

let interface_of (file_system_map:files_for_module_name) (key:module_name)
    : option<file_name> =
    match BU.smap_try_find file_system_map key with
    | Some (Some iface, _) -> Some iface
    | _ -> None

let implementation_of (file_system_map:files_for_module_name) (key:module_name)
    : option<file_name> =
    match BU.smap_try_find file_system_map key with
    | Some (_, Some impl) -> Some impl
    | _ -> None

let has_interface (file_system_map:files_for_module_name) (key:module_name)
    : bool =
    Option.isSome (interface_of file_system_map key)

let has_implementation (file_system_map:files_for_module_name) (key:module_name)
    : bool =
    Option.isSome (implementation_of file_system_map key)

(* In public interface *)
let cache_file_name fn =
  FStar.Options.prepend_cache_dir
    (if Options.lax()
     then fn ^ ".checked.lax"
     else fn ^ ".checked")

let file_of_dep_aux
                (use_checked_file:bool)
                (file_system_map:files_for_module_name)
                (all_cmd_line_files:list<file_name>)
                (d:dependence)
    : file_name =
    let cmd_line_has_impl key =
        all_cmd_line_files
        |> BU.for_some (fun fn ->
           is_implementation fn &&
           key = lowercase_module_name fn)
    in
    let maybe_add_suffix f = if use_checked_file then cache_file_name f else f in
    match d with
    | UseInterface key ->
      //This key always resolves to an interface source file
      (match interface_of file_system_map key with
       | None ->
         assert false; //should be unreachable; see the only use of UseInterface in discover_one
         raise_err (Errors.Fatal_MissingInterface, BU.format1 "Expected an interface for module %s, but couldn't find one" key)
       | Some f ->
         f)

    | PreferInterface key //key for module 'a'
        when has_interface file_system_map key ->  //so long as 'a.fsti' exists
      if cmd_line_has_impl key //unless the cmd line contains 'a.fst'
      && Option.isNone (Options.dep()) //and we're not just doing a dependency scan using `--dep _`
      then if Options.expose_interfaces()
           then maybe_add_suffix (Option.get (implementation_of file_system_map key))
           else raise_err (Errors.Fatal_MissingExposeInterfacesOption,
                           BU.format3 "You may have a cyclic dependence on module %s: use --dep full to confirm. \
                                       Alternatively, invoking fstar with %s on the command line breaks \
                                       the abstraction imposed by its interface %s; \
                                       if you really want this behavior add the option '--expose_interfaces'"
                                       key
                                       (Option.get (implementation_of file_system_map key))
                                       (Option.get (interface_of file_system_map key)))
      else maybe_add_suffix (Option.get (interface_of file_system_map key))   //we prefer to use 'a.fsti'

    | PreferInterface key
    | UseImplementation key
    | FriendImplementation key ->
        match implementation_of file_system_map key with
        | None ->
          //if d is actually an edge in the dep_graph computed by discover
          //then d is only present if either an interface or an implementation exist
          //the previous case already established that the interface doesn't exist
          //     since if the implementation was on the command line, it must exist because of option validation
          raise_err (Errors.Fatal_MissingImplementation,
                     BU.format1 "Expected an implementation of module %s, but couldn't find one" key)
        | Some f -> maybe_add_suffix f

let file_of_dep = file_of_dep_aux false

let dependences_of (file_system_map:files_for_module_name)
                   (deps:dependence_graph)
                   (all_cmd_line_files:list<file_name>)
                   (fn:file_name)
    : list<file_name> =
    match deps_try_find deps fn with
    | None -> empty_dependences
    | Some (deps, _) ->
      List.map (file_of_dep file_system_map all_cmd_line_files) deps

let print_graph (graph:dependence_graph) =
  Util.print_endline "A DOT-format graph has been dumped in the current directory as dep.graph";
  Util.print_endline "With GraphViz installed, try: fdp -Tpng -odep.png dep.graph";
  Util.print_endline "Hint: cat dep.graph | grep -v _ | grep -v prims";
  Util.write_file "dep.graph" (
    "digraph {\n" ^
    String.concat "\n" (List.collect
      (fun k ->
          let deps = fst (must (deps_try_find graph k)) in
          let r s = replace_char s '.' '_' in
          let print dep =
            Util.format2 "  \"%s\" -> \"%s\""
                (r (lowercase_module_name k))
                (r (module_name_of_dep dep))
          in
          List.map print deps)
     (List.unique (deps_keys graph))) ^
    "\n}\n"
  )

(** Enumerate all F* files in include directories.
    Return a list of pairs of long names and full paths. *)
(* In public interface *)
let build_inclusion_candidates_list (): list<(string * string)> =
  let include_directories = Options.include_path () in
  let include_directories = List.map normalize_file_path include_directories in
  (* Note that [BatList.unique] keeps the last occurrence, that way one can
   * always override the precedence order. *)
  let include_directories = List.unique include_directories in
  let cwd = normalize_file_path (getcwd ()) in
  List.concatMap (fun d ->
    if is_directory d then
      let files = readdir d in
      List.filter_map (fun f ->
        let f = basename f in
        check_and_strip_suffix f
        |> Util.map_option (fun longname ->
              let full_path = if d = cwd then f else join_paths d f in
              (longname, full_path))
      ) files
    else
      raise_err (Errors.Fatal_NotValidIncludeDirectory, (Util.format1 "not a valid include directory: %s\n" d))
  ) include_directories

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to pairs of filenames (/path/to/A.B.fst). Long names are
    all normalized to lowercase. The first component of the pair is the
    interface (if any). The second component of the pair is the implementation
    (if any). *)
let build_map (filenames: list<string>): files_for_module_name =
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

  (* Add files from all include directories *)
  List.iter (fun (longname, full_path) ->
    add_entry (String.lowercase longname) full_path
  ) (build_inclusion_candidates_list ());
  (* All the files we've been given on the command-line must be valid FStar files. *)
  List.iter (fun f ->
    add_entry (lowercase_module_name f) f
  ) filenames;
  map

(** For all items [i] in the map that start with [prefix], add an additional
    entry where [i] stripped from [prefix] points to the same value. Returns a
    boolean telling whether the map was modified. *)
let enter_namespace (original_map: files_for_module_name) (working_map: files_for_module_name) (prefix: string): bool =
  let found = BU.mk_ref false in
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

let namespace_of_lid l =
  String.concat "_" (List.map text_of_id l.ns)

let check_module_declaration_against_filename (lid: lident) (filename: string): unit =
  let k' = lowercase_join_longident lid true in
  if String.lowercase (must (check_and_strip_suffix (basename filename))) <> k' then
    FStar.Errors.log_issue (range_of_lid lid)
      (Errors.Error_ModuleFileNameMismatch, (Util.format2 "The module declaration \"module %s\" \
         found in file %s does not match its filename. Dependencies will be \
         incorrect and the module will not be verified.\n" (string_of_lid lid true) filename))

exception Exit

(* In public interface *)
let hard_coded_dependencies full_filename =
  let filename : string = basename full_filename in
  let corelibs =
    [Options.prims_basename () ;
     Options.pervasives_basename () ;
     Options.pervasives_native_basename ()]
  in
  (* The core libraries do not have any implicit dependencies *)
  if List.mem filename corelibs then []
  else let implicit_deps =
           [ (Const.fstar_ns_lid, Open_namespace);
             (Const.prims_lid, Open_module);
             (Const.pervasives_lid, Open_module) ] in
       match (namespace_of_module (lowercase_module_name full_filename)) with
       | None -> implicit_deps
       | Some ns -> implicit_deps @ [(ns, Open_namespace)]

let dep_subsumed_by d d' =
      match d, d' with
      | PreferInterface l', FriendImplementation l -> l=l'
      | _ -> d = d'

(** Parse a file, walk its AST, return a list of FStar lowercased module names
    it depends on. *)
let collect_one
  (original_map: files_for_module_name)
  (filename: string):
   list<dependence> //direct dependences of filename
 * list<dependence> //additional "roots" that should be scanned
                    //i.e. implementations of interfaces in the first list
 * bool             //interface that contains an `inline_for_extraction`
=
  let deps     : ref<(list<dependence>)> = BU.mk_ref [] in
  let mo_roots : ref<(list<dependence>)> = BU.mk_ref [] in
  let has_inline_for_extraction = BU.mk_ref false in
  let set_interface_inlining () =
      if is_interface filename
      then has_inline_for_extraction := true
  in
  let add_dep deps d =
    if not (List.existsML (dep_subsumed_by d) !deps) then
      deps := d :: !deps
  in
  let working_map = smap_copy original_map in

  let dep_edge module_name =
      PreferInterface module_name
  in

  let add_dependence_edge original_or_working_map lid =
    let key = lowercase_join_longident lid true in
    match resolve_module_name original_or_working_map key with
    | Some module_name ->
      add_dep deps (dep_edge module_name);
      if has_interface original_or_working_map module_name
      && has_implementation original_or_working_map module_name
      then add_dep mo_roots (UseImplementation module_name);
      true
    | _ ->
      false
  in

  let record_open_module let_open lid =
      //use the original_map here
      //since the working_map will resolve lid while accounting
      //for already opened namespaces
      //if let_open, then this is the form `UInt64.( ... )`
      //             where UInt64 can resolve to FStar.UInt64
      //           So, use the working map, accounting for opened namespaces
      //Otherwise, this is the form `open UInt64`,
      //           where UInt64 must resolve to either
      //           a module or a namespace for F# compatibility
      //           So, use the original map, disregarding opened namespaces
      if (let_open     && add_dependence_edge working_map lid)
      ||  (not let_open && add_dependence_edge original_map lid)
      then true
      else begin
        if let_open then
           FStar.Errors.log_issue (range_of_lid lid)
            (Errors.Warning_ModuleOrFileNotFoundWarning, (Util.format1 "Module not found: %s" (string_of_lid lid true)));
        false
      end
  in

  let record_open_namespace lid =
    let key = lowercase_join_longident lid true in
    let r = enter_namespace original_map working_map key in
    if not r then
        FStar.Errors.log_issue (range_of_lid lid)
          (Errors.Warning_ModuleOrFileNotFoundWarning, (Util.format1 "No modules in namespace %s and no file with \
            that name either" (string_of_lid lid true)))
  in

  let record_open let_open lid =
    if record_open_module let_open lid
    then ()
    else if not let_open //syntactically, this cannot be a namespace if let_open is true; so don't retry
    then record_open_namespace lid
  in

  let record_open_module_or_namespace (lid, kind) =
    match kind with
    | Open_namespace -> record_open_namespace lid
    | Open_module -> let _ = record_open_module false lid in ()
  in

  let record_module_alias ident lid =
    let key = String.lowercase (text_of_id ident) in
    let alias = lowercase_join_longident lid true in
    // Only fully qualified module aliases are allowed.
    match smap_try_find original_map alias with
    | Some deps_of_aliased_module ->
        smap_add working_map key deps_of_aliased_module;
        true
    | None ->
        FStar.Errors.log_issue (range_of_lid lid)
          (Errors.Warning_ModuleOrFileNotFoundWarning,  (Util.format1 "module not found in search path: %s\n" alias));
        false
  in

  let add_dep_on_module (module_name : lid) =
      if add_dependence_edge working_map module_name
      then ()
      else if Options.debug_any () then
            FStar.Errors.log_issue (range_of_lid module_name)
                (Errors.Warning_UnboundModuleReference, (BU.format1 "Unbound module reference %s"
                                (Ident.string_of_lid module_name)))
  in
  let record_lid lid =
    (* Thanks to the new `?.` and `.(` syntaxes, `lid` is no longer a
       module name itself, so only its namespace part is to be
       recorded as a module dependency.  *)
    match lid.ns with
    | [] -> ()
    | _ ->
      let module_name = Ident.lid_of_ids lid.ns in
      add_dep_on_module module_name
  in

  let auto_open = hard_coded_dependencies filename in
  List.iter record_open_module_or_namespace auto_open;

  let num_of_toplevelmods = BU.mk_ref 0 in

  let rec collect_module = function
    | Module (lid, decls)
    | Interface (lid, decls, _) ->
        check_module_declaration_against_filename lid filename;
        if List.length lid.ns > 0 then
          ignore (enter_namespace original_map working_map (namespace_of_lid lid));
        collect_decls decls

  and collect_decls decls =
    List.iter (fun x -> collect_decl x.d;
                        List.iter collect_term x.attrs;
                        if List.contains Inline_for_extraction x.quals
                        then set_interface_inlining()
                        ) decls

  and collect_decl d =
    match d with
    | Include lid
    | Open lid ->
        record_open false lid
    | Friend lid ->
        add_dep deps (FriendImplementation (lowercase_join_longident lid true))
    | ModuleAbbrev (ident, lid) ->
        if record_module_alias ident lid
        then add_dep deps (dep_edge (lowercase_join_longident lid true))
    | TopLevelLet (_, patterms) ->
        List.iter (fun (pat, t) -> collect_pattern pat; collect_term t) patterms
    | Main t
    | Splice (_, t)
    | Assume (_, t)
    | SubEffect { lift_op = NonReifiableLift t }
    | SubEffect { lift_op = LiftForFree t }
    | Val (_, t) ->
        collect_term t
    | SubEffect { lift_op = ReifiableLift (t0, t1) } ->
        collect_term t0;
        collect_term t1
    | Tycon (_, tc, ts) ->
        begin
        if tc then
            record_lid Const.mk_class_lid;
        let ts = List.map (fun (x,docnik) -> x) ts in
        List.iter collect_tycon ts
        end
    | Exception (_, t) ->
        iter_opt t collect_term
    | NewEffect ed ->
        collect_effect_decl ed
    | Fsdoc _
    | Pragma _ ->
        ()
    | TopLevelModule lid ->
        incr num_of_toplevelmods;
        if (!num_of_toplevelmods > 1) then
            raise_error (Errors.Fatal_OneModulePerFile, Util.format1 "Automatic dependency analysis demands one \
              module per file (module %s not supported)" (string_of_lid lid true)) (range_of_lid lid)
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
    | DefineEffect (_, binders, t, decls) ->
        collect_binders binders;
        collect_term t;
        collect_decls decls
    | RedefineEffect (_, binders, t) ->
        collect_binders binders;
        collect_term t

  and collect_binders binders =
    List.iter collect_binder binders

  and collect_binder b =
    collect_aqual b.aqual;
    match b with
    | { b = Annotated (_, t) }
    | { b = TAnnotated (_, t) }
    | { b = NoName t } -> collect_term t
    | _ -> ()

  and collect_aqual = function
    | Some (Meta t) -> collect_term t
    | _ -> ()

  and collect_term t =
    collect_term' t.tm

  and collect_constant = function
    | Const_int (_, Some (signedness, width)) ->
        let u = match signedness with | Unsigned -> "u" | Signed -> "" in
        let w = match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64" in
        add_dep deps (dep_edge (Util.format2 "fstar.%sint%s" u w))
    | Const_char _ ->
        add_dep deps (dep_edge "fstar.char")
    | Const_float _ ->
        add_dep deps (dep_edge "fstar.float")
    | _ ->
        ()

  and collect_term' = function
    | Wild ->
        ()
    | Const c ->
        collect_constant c
    | Op (s, ts) ->
        if Ident.text_of_id s = "@" then
          (* We use FStar.List.Tot.Base instead of FStar.List.Tot to prevent FStar.List.Tot.Properties from depending on FStar.List.Tot *)
          collect_term' (Name (lid_of_path (path_of_text "FStar.List.Tot.Base.append") Range.dummyRange));
        List.iter collect_term ts
    | Tvar _
    | AST.Uvar _ ->
        ()
    | Var lid
    | AST.Projector (lid, _)
    | AST.Discrim lid
    | Name lid ->
        record_lid lid
    | Construct (lid, termimps) ->
        if List.length termimps = 1 then
          record_lid lid;
        List.iter (fun (t, _) -> collect_term t) termimps
    | Abs (pats, t) ->
        collect_patterns pats;
        collect_term t
    | App (t1, t2, _) ->
        collect_term t1;
        collect_term t2
    | Let (_, patterms, t) ->
        List.iter (fun (attrs_opt, (pat, t)) ->
            ignore (BU.map_opt attrs_opt (List.iter collect_term));
            collect_pattern pat;
            collect_term t)
            patterms;
        collect_term t
    | LetOpen (lid, t) ->
        record_open true lid;
        collect_term t
    | Bind(_, t1, t2)
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
    | Ascribed (t1, t2, None) ->
        collect_term t1;
        collect_term t2
    | Ascribed (t1, t2, Some tac) ->
        collect_term t1;
        collect_term t2;
        collect_term tac
    | Record (t, idterms) ->
        iter_opt t collect_term;
        List.iter (fun (_, t) -> collect_term t) idterms
    | Project (t, _) ->
        collect_term t
    | Product (binders, t) ->
      collect_binders binders;
      collect_term t
    | Sum (binders, t) ->
        List.iter (function
          | Inl b -> collect_binder b
          | Inr t -> collect_term t)
          binders;
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
    | Quote (t, _)
    | Antiquote t
    | VQuote t ->
        collect_term t
    | Attributes cattributes  ->
        List.iter collect_term cattributes
    | CalcProof (rel, init, steps) ->
        (* TODO: add the Calc module too *)
        add_dep_on_module (Ident.lid_of_str "FStar.Calc");
        begin
        collect_term rel;
        collect_term init;
        List.iter (function CalcStep (rel, just, next) ->
            collect_term rel;
            collect_term just;
            collect_term next) steps
        end

  and collect_patterns ps =
    List.iter collect_pattern ps

  and collect_pattern p =
    collect_pattern' p.pat

  and collect_pattern' = function
    | PatVar (_, aqual)
    | PatTvar (_, aqual)
    | PatWild aqual ->
        collect_aqual aqual

    | PatOp _
    | PatConst _ ->
        ()
    | PatApp (p, ps) ->
        collect_pattern p;
        collect_patterns ps
    | PatName _ ->
        ()
    | PatList ps
    | PatOr ps
    | PatTuple (ps, _) ->
        collect_patterns ps
    | PatRecord lidpats ->
        List.iter (fun (_, p) -> collect_pattern p) lidpats
    | PatAscribed (p, (t, None)) ->
        collect_pattern p;
        collect_term t
    | PatAscribed (p, (t, Some tac)) ->
        collect_pattern p;
        collect_term t;
        collect_term tac


  and collect_branches bs =
    List.iter collect_branch bs

  and collect_branch (pat, t1, t2) =
    collect_pattern pat;
    iter_opt t1 collect_term;
    collect_term t2

  in
  let ast, _ = Driver.parse_file filename in
  let mname = lowercase_module_name filename in
  if is_interface filename
  && has_implementation original_map mname
  then add_dep mo_roots (UseImplementation mname);
  collect_module ast;
  (* Util.print2 "Deps for %s: %s\n" filename (String.concat " " (!deps)); *)
  !deps, !mo_roots, !has_inline_for_extraction


(* JP: it looks like the code was changed but the comments were never updated.
 * In particular, we no longer compute transitive dependencies, and we no longer
 * map lowercase module names to filenames. *)

// Used by F*.js
let collect_one_cache : ref<(smap<(list<dependence> * list<dependence> * bool)>)> =
  BU.mk_ref (BU.smap_create 0)

let set_collect_one_cache (cache: smap<(list<dependence> * list<dependence> * bool)>) : unit =
  collect_one_cache := cache

let dep_graph_copy dep_graph =
    let (Deps g) = dep_graph in
    Deps (BU.smap_copy g)

let topological_dependences_of
        file_system_map
        dep_graph
        interfaces_needing_inlining
        root_files
        for_extraction
    : list<file_name>
    * bool =
    let rec all_friend_deps_1
            dep_graph
            (cycle:list<file_name>)
            (all_friends, all_files)
            filename =
    let direct_deps, color = must (deps_try_find dep_graph filename) in
    match color with
    | Gray ->
        failwith "Impossible: cycle detected after cycle detection has passed"
    | Black ->
        (* If the element has been visited already, then the map contains all its
            * dependencies. Otherwise, the map only contains its direct dependencies. *)
        all_friends, all_files
    | White ->
        if Options.debug_any()
        then BU.print2 "Visiting %s: direct deps are %s\n"
                filename
                (String.concat ", " (List.map dep_to_string direct_deps));
        (* Unvisited. Compute. *)
        deps_add_dep dep_graph filename (direct_deps, Gray);
        let all_friends, all_files =
            all_friend_deps
                dep_graph cycle (all_friends, all_files)
                (dependences_of file_system_map
                                dep_graph
                                root_files
                                filename)
        in
        (* Mutate the graph to mark the node as visited *)
        deps_add_dep dep_graph filename (direct_deps, Black);
        if Options.debug_any()
        then BU.print1 "Adding %s\n" filename;
        (* Also build the topological sort (Tarjan's algorithm). *)
        List.collect
          (function | FriendImplementation m -> [m]
                    | d -> [])
          direct_deps
        @all_friends,
        filename :: all_files
    and all_friend_deps dep_graph cycle all_friends filenames =
        List.fold_left
                (fun all_friends k ->
                        all_friend_deps_1 dep_graph (k :: cycle) all_friends k)
                all_friends
                filenames
    in

    (* An important requirement is that in addition to files being
       emitted in topological order, we require implementation files
       to immmediately follow their interface files (if any) in the
       final order.

       This is because the interleaving semantics of
       interfaces+implementation relies on these files being adjacent
       in the dependence order.

       This is enforced in several steps.

       First, every implementation file contains its interface file as
       its *LAST* dependence. In a simple scenario, when scanning an
       the dependences of an implementation file, we will encounter
       its interface last, and so we would complete the dependence
       scan of all the dependences of the implementation;then the
       dependences of the interface file; then emit the interface file
       in the topological sort (above); followed immediately by the
       implementation.

       More complex situations arise due to friend modules where some
       modules in the dependence graph may rely only on the module's
       interface, whereas others may rely on its implementation.

       Further complications arise from cross-module inlining, where,
       the extraction of one module may depend on the implementation
       details of another module.

       To handle this, we compute the file list in several phases:

        1. If --cmi and codegen is true, then we need to inline across
           interface boundaries for modules M that are in the
           interfaces_needing_inlining list. So, we transform the
           dependence graph updating every interface dependence on
           such a module M into a friend dependence on that module's
           implementation.

        2. Then, we traverse the graph in topological order
           encountering all friend modules reachable from the
           specified roots.

        3. Then, we alter the dependences to turn every occurrence of
           a interface dependence of a friend module into an
           implementation dependence. Note, this does not change the
           set of files reachable from the given roots.

        4. A second traversal now collects all the files in dependence
           order, ensuring that implementation and interface files are
           adjacent in the dependence order, since the interface is
           always the last dependence of an implementation.

       This ensures that for a given set of roots, every module that
       needs to be friended or inlined is marked as a friend for
       *every* module in the dependence graph, avoiding "double
       vision" problems of some modules seeing the interface only
       whereas others requiring both interface+implementation.

       So, when traversing the graph, we always encounter friend
       module implementaions first, then their interfaces, emitting
       them adjacent to the each other in the final order.
    *)

    if Options.debug_any()
    then BU.print_string "==============Phase1==================\n";
    let widened = BU.mk_ref false in
    let widen_deps friends deps =
        let (Deps dg) = deps in
        let (Deps dg') = deps_empty() in
        let widen_one deps =
          deps |> List.map (fun d ->
            match d with
            | PreferInterface m
                when (List.contains m friends &&
                     has_implementation file_system_map m) ->
              widened := true;
              FriendImplementation m
            | _ -> d)
        in
        BU.smap_fold
           dg
           (fun filename (dependences, color) () ->
              BU.smap_add
                dg'
                filename
                (widen_one dependences, White))
           ();
        Deps dg'
    in
    let dep_graph =
      if Options.cmi()
      && for_extraction
      then widen_deps interfaces_needing_inlining dep_graph
      else dep_graph
    in
    let friends, all_files_0 =
        all_friend_deps dep_graph [] ([], []) root_files
    in
    if Options.debug_any()
    then BU.print3 "Phase1 complete:\n\t\
                       all_files = %s\n\t\
                       all_friends=%s\n\t\
                       interfaces_with_inlining=%s\n"
                   (String.concat ", " all_files_0)
                   (String.concat ", " (remove_dups (fun x y -> x=y) friends))
                   (String.concat ", " (interfaces_needing_inlining));
    let dep_graph = widen_deps friends dep_graph in
    let _, all_files =
        if Options.debug_any()
        then BU.print_string "==============Phase2==================\n";
        all_friend_deps dep_graph [] ([], []) root_files
    in
    if Options.debug_any()
    then BU.print1 "Phase2 complete: all_files = %s\n" (String.concat ", " all_files);
    all_files,
    !widened

(** Collect the dependencies for a list of given files.
    And record the entire dependence graph in the memoized state above **)
(* In public interface *)
let collect (all_cmd_line_files: list<file_name>)
    : list<file_name>
    * deps //topologically sorted transitive dependences of all_cmd_line_files
    =

  let all_cmd_line_files =
      all_cmd_line_files |> List.map (fun fn ->
        match FStar.Options.find_file fn with
        | None ->
          Errors.raise_err (Errors.Fatal_ModuleOrFileNotFound,
                            Util.format1 "File %s could not be found\n" fn)
        | Some fn -> fn) in
  (* The dependency graph; keys are lowercased module names, values = list of
   * lowercased module names this file depends on. *)
  let dep_graph : dependence_graph = deps_empty () in

  (* A map from lowercase module names (e.g. [a.b.c]) to the corresponding
   * filenames (e.g. [/where/to/find/A.B.C.fst]). Consider this map
   * immutable from there on. *)
  let file_system_map = build_map all_cmd_line_files in

  let interfaces_needing_inlining = BU.mk_ref [] in
  let add_interface_for_inlining l =
    let l = lowercase_module_name l in
    interfaces_needing_inlining := l :: !interfaces_needing_inlining
  in

  (* discover: Do a graph traversal starting from file_name
   *           filling in dep_graph with the dependences *)
  let rec discover_one (file_name:file_name) =
    if deps_try_find dep_graph file_name = None then
    begin
      let deps, mo_roots, needs_interface_inlining =
        match BU.smap_try_find !collect_one_cache file_name with
        | Some cached -> cached
        | None -> collect_one file_system_map file_name in
      if needs_interface_inlining
      then add_interface_for_inlining file_name;
      let deps =
          let module_name = lowercase_module_name file_name in
          if is_implementation file_name
          && has_interface file_system_map module_name
          then deps @ [UseInterface module_name]
          else deps
      in
      deps_add_dep dep_graph file_name (List.unique deps, White);
      List.iter
            discover_one
            (List.map (file_of_dep file_system_map all_cmd_line_files)
                      (deps @ mo_roots))
    end
  in
  List.iter discover_one all_cmd_line_files;

  (* At this point, dep_graph has all the (immediate) dependency graph of all the files. *)
  let cycle_detected dep_graph cycle filename =
      Util.print1 "The cycle contains a subset of the modules in:\n%s \n" (String.concat "\n`used by` " cycle);
      print_graph dep_graph;
      print_string "\n";
      Errors.raise_err (Errors.Fatal_CyclicDependence,
                        BU.format1 "Recursive dependency on module %s\n" filename)
  in
  (* full_cycle_detection finds cycles across interface
     boundaries that can otherwise be exploited to
     build cross-module recursive loops, as in issue #1391
  *)
  let full_cycle_detection all_command_line_files =
    let dep_graph = dep_graph_copy dep_graph in
    let rec aux (cycle:list<file_name>) filename =
        let direct_deps, color =
            match deps_try_find dep_graph filename with
            | Some (d, c) -> d, c
            | None ->
              failwith (BU.format1 "Failed to find dependences of %s" filename)
        in
        let direct_deps = direct_deps |> List.collect (fun x ->
            match x with
            | UseInterface f
            | PreferInterface f ->
              begin
              match implementation_of file_system_map f with
              | None -> [x]
              | Some fn when fn=filename ->
                //don't add trivial self-loops
                [x]
              | _ ->
                //if a module A uses B
                //then detect cycles through both B.fsti
                //and B.fst
               [x; UseImplementation f]
              end
            | _ -> [x]) in
        match color with
        | Gray ->
           cycle_detected dep_graph cycle filename
        | Black ->
            (* If the element has been visited already, then the map contains all its
             * dependencies. Otherwise, the map only contains its direct dependencies. *)
            ()
        | White ->
            (* Unvisited. Compute. *)
            deps_add_dep dep_graph filename (direct_deps, Gray);
            List.iter (fun k -> aux (k :: cycle) k)
                      (dependences_of file_system_map
                                      dep_graph
                                      all_command_line_files
                                      filename);
            (* Mutate the graph (to mark the node as visited) *)
            deps_add_dep dep_graph filename (direct_deps, Black)
      in
      List.iter (aux []) all_command_line_files
  in
  full_cycle_detection all_cmd_line_files;

  //only verify those files on the command line
  all_cmd_line_files |>
  List.iter (fun f ->
    let m = lowercase_module_name f in
    Options.add_verify_module m);

  let inlining_ifaces = !interfaces_needing_inlining in
  let all_files, _ =
    topological_dependences_of
      file_system_map
      dep_graph
      inlining_ifaces
      all_cmd_line_files
      (Options.codegen()<>None)
  in
  if Options.debug_any()
  then BU.print1 "Interfaces needing inlining: %s\n" (String.concat ", " inlining_ifaces);
  all_files,
  mk_deps dep_graph file_system_map all_cmd_line_files all_files inlining_ifaces

(* In public interface *)
let deps_of deps (f:file_name)
    : list<file_name> =
    dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f

(* In public interface *)
let hash_dependences deps fn =
    let file_system_map = deps.file_system_map in
    let all_cmd_line_files = deps.cmd_line_files in
    let deps = deps.dep_graph in
    let fn =
        match FStar.Options.find_file fn with
        | Some fn -> fn
        | _ -> fn
    in
    let cache_file = cache_file_name fn in
    let digest_of_file fn =
        if Options.debug_any()
        then BU.print2 "%s: contains digest of %s\n" cache_file fn;
        BU.digest_of_file fn
    in
    let module_name = lowercase_module_name fn in
    let source_hash = digest_of_file fn in
    let interface_hash =
        if is_implementation fn
        && has_interface file_system_map module_name
        then ["interface", digest_of_file (Option.get (interface_of file_system_map module_name))]
        else []
    in
    let binary_deps = dependences_of file_system_map deps all_cmd_line_files fn
                |> List.filter (fun fn ->
                not (is_interface fn &&
                    lowercase_module_name fn = module_name)) in
    let binary_deps =
        FStar.List.sortWith
          (fun fn1 fn2 ->
             String.compare (lowercase_module_name fn1)
                            (lowercase_module_name fn2))
        binary_deps in
    let rec hash_deps out = function
        | [] -> Some (("source", source_hash)::interface_hash@out)
        | fn::deps ->
          let digest =
            let fn = cache_file_name fn in
            if BU.file_exists fn
            then Some (digest_of_file fn)
            else match FStar.Options.find_file (FStar.Util.basename fn) with
                 | None -> None
                 | Some fn -> Some (digest_of_file fn)
          in
          match digest with
          | None ->
            if Options.debug_any()
            then BU.print2 "%s: missed digest of file %s\n" cache_file (cache_file_name fn);
            None
          | Some dig ->
            hash_deps ((lowercase_module_name fn, dig) :: out) deps
    in
    hash_deps [] binary_deps

(* In public interface *)
let print_digest (dig:list<(string * string)>) : string =
    dig
    |> List.map (fun (m, d) -> BU.format2 "%s:%s" m (BU.base64_encode d))
    |> String.concat "\n"

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

    Deprecated: this will print the dependences among the source files
  *)
let print_make deps : unit =
    let file_system_map = deps.file_system_map in
    let all_cmd_line_files = deps.cmd_line_files in
    let deps = deps.dep_graph in
    let keys = deps_keys deps in
    keys |> List.iter
        (fun f ->
          let f_deps, _ = deps_try_find deps f |> Option.get in
          let files = List.map (file_of_dep file_system_map all_cmd_line_files) f_deps in
          let files = List.map (fun s -> replace_chars s ' ' "\\ ") files in
          //this one prints:
          //   a.fst: b.fst c.fsti a.fsti
          Util.print2 "%s: %s\n\n" f (String.concat " " files))

(* In public interface *)
let print_raw (deps:deps) =
    let (Deps deps) = deps.dep_graph in
      smap_fold deps (fun k (dep, _) out ->
        BU.format2 "%s -> [\n\t%s\n] " k (List.map dep_to_string dep |> String.concat ";\n\t") :: out) []
      |> String.concat ";;\n"
      |> BU.print_endline

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

     -- The dependences are among the .checked files

     -- We also print dependences for producing .ml files from .checked files
        This takes care of renaming A.B.C.fst to A_B_C.ml
  *)
let print_full (deps:deps) : unit =
    //let (Mk (deps, file_system_map, all_cmd_line_files, all_files)) = deps in
    let sort_output_files (orig_output_file_map:BU.smap<string>) =
        let order : ref<(list<string>)> = BU.mk_ref [] in
        let remaining_output_files = BU.smap_copy orig_output_file_map in
        let visited_other_modules = BU.smap_create 41 in
        let should_visit lc_module_name =
            Option.isSome (BU.smap_try_find remaining_output_files lc_module_name)
            || Option.isNone (BU.smap_try_find visited_other_modules lc_module_name)
        in
        let mark_visiting lc_module_name =
            let ml_file_opt = BU.smap_try_find remaining_output_files lc_module_name in
            BU.smap_remove remaining_output_files lc_module_name;
            BU.smap_add visited_other_modules lc_module_name true;
            ml_file_opt
        in
        let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | None -> ()
            | Some ml_file -> order := ml_file :: !order
        in
        let rec aux = function
            | [] -> ()
            | lc_module_name::modules_to_extract ->
              let visit_file file_opt =
                match file_opt with
                | None -> ()
                | Some file_name ->
                  match deps_try_find deps.dep_graph file_name with
                  | None -> failwith (BU.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
                  | Some (immediate_deps, _) ->
                    let immediate_deps =
                        List.map (fun x -> String.lowercase (module_name_of_dep x)) immediate_deps
                    in
                    aux immediate_deps
              in
              if should_visit lc_module_name then begin
                 let ml_file_opt = mark_visiting lc_module_name in
                 //visit all its dependences
                 visit_file (implementation_of deps.file_system_map lc_module_name);
                 visit_file (interface_of deps.file_system_map lc_module_name);
                 //and then emit this one's ML file
                 emit_output_file_opt ml_file_opt
              end;
              aux modules_to_extract
        in
        let all_extracted_modules = BU.smap_keys orig_output_file_map in
        aux all_extracted_modules;
        List.rev !order
    in
    let keys = deps_keys deps.dep_graph in
    let output_file ext fst_file =
        let ml_base_name = replace_chars (Option.get (check_and_strip_suffix (BU.basename fst_file))) '.' "_" in
        Options.prepend_output_dir (ml_base_name ^ ext)
    in
    let norm_path s = replace_chars s '\\' "/" in
    let output_ml_file f = norm_path (output_file ".ml" f) in
    let output_krml_file f = norm_path (output_file ".krml" f) in
    let output_cmx_file f = norm_path (output_file ".cmx" f) in
    let cache_file f = norm_path (cache_file_name f) in
    let transitive_krml = smap_create 41 in
    keys |> List.iter
        (fun file_name ->
          let f_deps, _ = deps_try_find deps.dep_graph file_name |> Option.get in
          let iface_deps =
              if is_interface file_name
              then None
              else match interface_of deps.file_system_map (lowercase_module_name file_name) with
                   | None ->
                     None
                   | Some iface ->
                     Some (fst (Option.get (deps_try_find deps.dep_graph iface)))
          in
          let iface_deps =
              BU.map_opt iface_deps
                         (List.filter (fun iface_dep ->
                             not (BU.for_some (dep_subsumed_by iface_dep) f_deps)))
          in
          let norm_f = norm_path file_name in
          let files = List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) f_deps in
          let files =
              match iface_deps with
              | None -> files
              | Some iface_deps ->
                let iface_files =
                    List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) iface_deps
                in
                BU.remove_dups (fun x y -> x = y) (files @ iface_files)
          in
          let files = List.map norm_path files in
          let files = List.map (fun s -> replace_chars s ' ' "\\ ") files in
          let files = String.concat "\\\n\t" files in

          //this one prints:
          //   a.fst.checked: b.fst.checked c.fsti.checked a.fsti
          Util.print3 "%s: %s \\\n\t%s\n\n"
                      (cache_file file_name)
                      norm_f
                      files;

          // for building an executable from a given module:
          // foo.exe: dep1.krml dep2.krml etc.
          let already_there =
            match smap_try_find transitive_krml (norm_path (output_file ".krml" file_name)) with
            | Some (_, already_there, _) -> already_there
            | None -> []
          in
          smap_add transitive_krml
            (norm_path (output_file ".krml" file_name))
            (norm_path (output_file ".exe" file_name),
              List.unique (already_there @ List.map
                (fun x -> norm_path (output_file ".krml" x))
                (deps_of deps file_name)),
              false);

          //And, if this is not an interface, we also print out the dependences among the .ml files
          // excluding files in ulib, since these are packaged in fstarlib.cmxa
        let all_fst_files_dep, widened =
            if Options.cmi()
            then topological_dependences_of
                    deps.file_system_map
                    deps.dep_graph
                    deps.interfaces_with_inlining
                    [file_name]
                    true
            else
                let maybe_widen_deps (f_deps:dependences) =
                    List.map
                        (fun dep ->
                         file_of_dep_aux false deps.file_system_map deps.cmd_line_files dep)
                    f_deps
                in
                let fst_files = maybe_widen_deps f_deps in
                let fst_files_from_iface =
                    match iface_deps with
                    | None -> []
                    | Some iface_deps -> maybe_widen_deps iface_deps
                in
                BU.remove_dups (fun x y -> x = y) (fst_files @ fst_files_from_iface),
                false
        in
        let all_checked_fst_files = List.map cache_file all_fst_files_dep in
          if is_implementation file_name then (
            if Options.cmi()
            && widened
            then begin
                Util.print3 "%s: %s \\\n\t%s\n\n"
                            (output_ml_file file_name)
                            (cache_file file_name)
                            (String.concat " \\\n\t" all_checked_fst_files);
                Util.print3 "%s: %s \\\n\t%s\n\n"
                            (output_krml_file file_name)
                            (cache_file file_name)
                            (String.concat " \\\n\t" all_checked_fst_files)
            end
            else begin
                Util.print2 "%s: %s \n\n"
                            (output_ml_file file_name)
                            (cache_file file_name);
                Util.print2 "%s: %s\n\n"
                            (output_krml_file file_name)
                            (cache_file file_name)
            end;
            let cmx_files =
                let extracted_fst_files =
                    all_fst_files_dep |> List.filter (fun df ->
                        lowercase_module_name df <> lowercase_module_name file_name //avoid circular deps on f's own cmx
                        && Options.should_extract (lowercase_module_name df))
                in
                extracted_fst_files |> List.map output_cmx_file
            in
            if Options.should_extract (lowercase_module_name file_name)
            then Util.print3 "%s: %s \\\n\t%s\n\n"
                        (output_cmx_file file_name)
                        (output_ml_file file_name)
                        (String.concat "\\\n\t" cmx_files)
          ) else if not(has_implementation deps.file_system_map (lowercase_module_name file_name))
                 && is_interface file_name then (
            // .krml files can be produced using just an interface, unlike .ml files
            if Options.cmi()
            && widened
            then
                Util.print3 "%s: %s \\\n\t%s\n\n"
                            (output_krml_file file_name)
                            (cache_file file_name)
                            (String.concat " \\\n\t" all_checked_fst_files)
            else
                Util.print2 "%s: %s \n\n"
                    (output_krml_file file_name)
                    (cache_file file_name)
          ));
    let all_fst_files = keys |> List.filter is_implementation |> Util.sort_with String.compare in
    let all_ml_files =
        let ml_file_map = BU.smap_create 41 in
        all_fst_files
        |> List.iter (fun fst_file ->
                       let mname = lowercase_module_name fst_file in
                       if Options.should_extract mname
                       then BU.smap_add ml_file_map mname (output_ml_file fst_file));
        sort_output_files ml_file_map
    in
    let all_krml_files =
        let krml_file_map = BU.smap_create 41 in
        keys
        |> List.iter (fun fst_file ->
                       let mname = lowercase_module_name fst_file in
                       BU.smap_add krml_file_map mname (output_krml_file fst_file));
        sort_output_files krml_file_map
    in
    // compute transitive closure for dependency graphs that contain multiple
    // entry points
    let rec make_transitive f =
      let exe, deps, seen = must (smap_try_find transitive_krml f) in
      if seen then
        exe, deps
      else begin
        (* JP: avoid loops for nodes that point to themselves via their
         * interface. *)
        smap_add transitive_krml f (exe, deps, true);
        let deps = List.unique (List.flatten (List.map (fun dep ->
          let _, deps = make_transitive dep in
          dep :: deps
        ) deps)) in
        smap_add transitive_krml f (exe, deps, true);
        exe, deps
      end
    in
    List.iter (fun f ->
      let exe, deps = make_transitive f in
      let deps = String.concat " " (List.unique (f :: deps)) in
      let wasm = BU.substring exe 0 (String.length exe - 4) ^ ".wasm" in
      Util.print2 "%s: %s\n\n" exe deps;
      Util.print2 "%s: %s\n\n" wasm deps
    ) (smap_keys transitive_krml);

    Util.print1 "ALL_FST_FILES=\\\n\t%s\n\n"  (all_fst_files  |> List.map norm_path |> String.concat " \\\n\t");
    Util.print1 "ALL_ML_FILES=\\\n\t%s\n\n"   (all_ml_files   |> List.map norm_path |> String.concat " \\\n\t");
    Util.print1 "ALL_KRML_FILES=\\\n\t%s\n"   (all_krml_files |> List.map norm_path |> String.concat " \\\n\t")

(* In public interface *)
let print deps =
  match Options.dep() with
  | Some "make" ->
      print_make deps
  | Some "full" ->
      print_full deps
  | Some "graph" ->
      print_graph deps.dep_graph
  | Some "raw" ->
      print_raw deps
  | Some _ ->
      raise_err (Errors.Fatal_UnknownToolForDep, "unknown tool for --dep\n")
  | None ->
      assert false

let print_fsmap fsmap =
    smap_fold fsmap (fun k (v0, v1) s ->
        s
        ^ "; "
        ^ BU.format3 "%s -> (%s, %s)"
                k (BU.dflt "_" v0) (BU.dflt "_" v1))
        ""

(* In public interface *)
let module_has_interface deps module_name =
    has_interface deps.file_system_map (String.lowercase (Ident.string_of_lid module_name))

(* In public interface *)
let deps_has_implementation deps module_name =
    let m = String.lowercase (Ident.string_of_lid module_name) in
    deps.all_files |> BU.for_some (fun f ->
        is_implementation f
        && String.lowercase (module_name_of_file f) = m)

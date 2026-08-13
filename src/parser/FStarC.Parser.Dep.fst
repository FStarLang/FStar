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
    It also supports scanning individual AST declarations for dependences.
    It is used in many parts of the compiler, including
     * to output a .depend for use with Makefiles, using fstar --dep
     * to check for the dependences of a checked file, used to write out their hashes
     * to scan dependences of a declarations on the fly, for use with fly_deps
    etc.
*)
module FStarC.Parser.Dep

open FStarC.Util { out_channel }
open FStarC.Ident
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Parser.AST
open FStarC.Const
open FStarC.Errors
open FStarC.Class.Show
open FStarC.Class.Ord
open FStarC.RBSet
open FStarC.Util

module Const = FStarC.Parser.Const
module BU = FStarC.Util
module F = FStarC.Format

let fd_enabled = mk_ref (None #bool)

let debug_fly_deps =
  let dbg = FStarC.Debug.get_toggle "fly_deps" in
  fun () -> !dbg

let fly_deps_enabled () =
    match !fd_enabled with
    | Some b -> b
    | None -> 
      let res = 
        if Options.Ext.enabled "fly_deps"
        then (
          if Some? <| Options.dep() //if we're doing dep, then we want a full scan now
          //dump_module: it's a debug feature, but Vale also depends on its output
          //so don't change that yet
          || Options.any_dump_module()
          then (
            if debug_fly_deps ()
            then (
              Format.print_string "Ignoring fly_deps because dep or dump_module is on\n"
            );
            false
          )
          else (
            if debug_fly_deps () then Format.print_string "fly_deps is on!\n";
            true
          )
        )
        else (
          if debug_fly_deps () then Format.print_string "fly_deps is off!\n";
          false
        )
      in
      Format.flush_stdout();
      fd_enabled := Some res;
      res

let with_fly_deps_disabled (f: unit -> ML 'a) : ML 'a =
  let v = !fd_enabled in
  fd_enabled := Some false;
  FStarC.Util.finally (fun _ -> fd_enabled := v) f

(* This is faster than the quadratic BU.remove_dups, since we can use
the total order. *)
let remove_dups_fast (#a:Type) {| ord a |} (xs : list a) : ML (list a) =
  let (acc, _) =
    List.fold_left (fun (acc, acc_set) x ->
      if mem x acc_set
      then (acc, acc_set)
      else (x::acc, add x acc_set)) ([], empty #a #(RBSet.t a) ()) xs
  in
  List.rev acc

let dbg              = Debug.get_toggle "Dep"
let dbg_CheckedFiles = Debug.get_toggle "CheckedFiles"
let debug_print (f: unit -> ML unit) : ML unit = if !dbg then f ()
let profile f c = Profiling.profile f None c

(* Meant to write to a file as an out_channel. If an exception is raised,
the file is deleted. *)
let with_file_outchannel (fn : string) (k : out_channel -> ML 'a) : ML 'a =
  BU.maybe_create_parent fn;
  let outc = BU.open_file_for_writing fn in
  let r =
    try k outc
    with | e -> BU.close_out_channel outc; BU.delete_file fn; raise e
  in
  BU.close_out_channel outc;
  r

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

type intf_and_impl = option string & option string

type files_for_module_name = SMap.t intf_and_impl

let intf_and_impl_to_string ii =
  match ii with
  | None, None -> "<None>, <None>"
  | Some intf, None -> intf
  | None, Some impl -> impl
  | Some intf, Some impl -> intf ^ ", " ^ impl


let files_for_module_name_to_string (m:files_for_module_name) =
  Format.print_string "Printing the file system map {\n";
  let str_opt_to_string sopt =
    match sopt with
    | None -> "<None>"
    | Some s -> s in
  SMap.iter m (fun k v -> Format.print2 "%s:%s\n" k (intf_and_impl_to_string v));
  Format.print_string "}\n"

type color = | White | Gray | Black

let all_file_suffixes () =
  let lang_exts = List.map (fun ext -> "." ^ ext) (FStarC.Options.lang_extensions ()) in
  let base = ".fst" :: lang_exts in
  base @ List.map (fun ext -> ext ^ "i") base

let check_and_strip_suffix (f: string): ML (option string) =
  let matches = List.map (fun ext ->
    let lext = String.length ext in
    let l = String.length f in
    if l > lext && String.substring f (l - lext) lext = ext then
      Some (String.substring f 0 (l - lext))
    else
      None
  ) (all_file_suffixes ()) in
  match List.filter Some? matches with
  | Some m :: _ ->
      Some m
  | _ ->
      None

(* In public interface *)
let is_interface (f: string): ML bool =
  String.get f (String.length f - 1) = 'i'
let implementation_of_file f =
  if is_interface f then 
    String.substring f 0 (String.length f - 1)
  else f
(* In public interface *)
let is_implementation f =
  not (is_interface f)

type parsing_data = {
    elts : list parsing_data_elt;
    no_prelude : bool;
}


let list_of_option = function Some x -> [x] | None -> []

let list_of_pair (intf, impl) =
  list_of_option intf @ list_of_option impl

(* Given a source file path, if it lives (possibly transitively, through
   subdirectories) under one of the include directories, recover its full
   dotted module name. We match against the *longest* include directory that is
   a path-boundary prefix of the file and turn the remaining relative path into
   a dotted name: an include directory [d] and a file [d/X/Y/Z.fst] yield
   "X.Y.Z". Returns None if the file is not under any include directory or is
   not a valid F* source file. *)
let module_name_from_include_path (f:string) : ML (option string) =
  let f = Filepath.normalize_file_path f in
  let include_dirs = List.map Filepath.normalize_file_path (Find.full_include_path ()) in
  let best =
    List.fold_left (fun (acc:option string) d ->
      if Util.starts_with f (d ^ "/")
      && (match acc with Some a -> String.length d > String.length a | None -> true)
      then Some d
      else acc)
      None include_dirs
  in
  match best with
  | None -> None
  | Some d ->
    let rel = Util.substring_from f (String.length d + 1) in
    match check_and_strip_suffix rel with
    | None -> None
    | Some stem -> Some (Util.replace_char (Util.replace_char stem '\\' '.') '/' '.')

(* In public interface *)
let maybe_module_name_of_file f =
  match module_name_from_include_path f with
  | Some longname -> Some longname
  | None -> check_and_strip_suffix (Filepath.basename f)
let module_name_of_file f =
    match maybe_module_name_of_file f with
    | Some longname ->
      longname
    | None ->
      raise_error0 Errors.Fatal_NotValidFStarFile (
        [ text <| Format.fmt1 "Not a valid FStar file: ‘%s’" f; ] @
        (if Platform.windows && f = ".." then [
          text <| "Note: In Windows-compiled versions of F*, a literal
          asterisk as argument will be expanded to a list of files,
          **even if quoted**. It is possible you provided such an
          argument which got expanded to the list of all files in this
          directory, causing spurious arguments that F* attempts to interpret as files.";
          text <| "Hint: did you perhaps pass --already_cached '*' or similar? You can add
          a comma (',*') to prevent the expansion and retain the behavior.";
        ] else [])
      )

(* In public interface *)
let lowercase_module_name f = String.lowercase (module_name_of_file f)

let namespace_of_module f =
    let lid = Ident.lid_of_path (Ident.path_of_text f) Range.dummyRange in
    match ns_of_lid lid with
    | [] -> None
    | ns -> Some (Ident.lid_of_ids ns)

type file_name = string
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
instance showable_dependence : showable dependence = {
  show = dep_to_string;
}

type dependences = list dependence
let empty_dependences = []
type dep_node = {
    edges:dependences;
    color:color
}
type dependence_graph = //maps file names to the modules it depends on
     | Deps of SMap.t dep_node //(dependences * color)>
let copy_dep_graph (d:dependence_graph) =
  let Deps m = d in Deps (SMap.copy m)

let str_of_parsing_data_elt elt =
  let str_of_open_kind = function
    | Open_module -> "P_open_module"
    | Open_namespace -> "P_open_namespace"
  in
  match elt with
  | P_begin_module lid -> "P_begin_module (" ^ (string_of_lid lid) ^ ")"
  | P_open (b, lid) -> "P_open (" ^ (show b) ^ ", " ^ (string_of_lid lid) ^ ")"
  | P_implicit_open_module_or_namespace (k, lid) -> "P_implicit_open_module_or_namespace (" ^ (str_of_open_kind k) ^ ", " ^ (string_of_lid lid) ^ ")"
  | P_dep (b, lid) -> "P_dep (" ^ (string_of_lid lid) ^ ", " ^ (show b) ^ ")"
  | P_alias (id, lid) -> "P_alias (" ^ (string_of_id id) ^ ", " ^ (string_of_lid lid) ^ ")"
  | P_lid lid -> "P_lid (" ^ (string_of_lid lid) ^ ")"
  | P_inline_for_extraction -> "P_inline_for_extraction"

instance showable_parsing_data_elt : showable parsing_data_elt = {
  show = str_of_parsing_data_elt;
}

let str_of_parsing_data pd =
  "{ elts = " ^ show pd.elts ^
  "; no_prelude = " ^ show pd.no_prelude ^
  "}"

instance showable_parsing_data : showable parsing_data = {
  show = str_of_parsing_data;
}

let friends (p:parsing_data) : ML (list lident) =
  List.collect
    (function
      | P_dep (true, l) -> [l]
      | _ -> [])
    p.elts

let parsing_data_elt_eq (e1:parsing_data_elt) (e2:parsing_data_elt) =
  match e1, e2 with
  | P_begin_module l1, P_begin_module l2 -> lid_equals l1 l2
  | P_open (b1, l1), P_open (b2, l2) -> b1 = b2 && lid_equals l1 l2
  | P_implicit_open_module_or_namespace (k1, l1), P_implicit_open_module_or_namespace (k2, l2) ->
    k1 = k2 && lid_equals l1 l2
  | P_dep (b1, l1), P_dep (b2, l2) -> b1 = b2 && lid_equals l1 l2
  | P_alias (i1, l1), P_alias (i2, l2) -> string_of_id i1 = string_of_id i2 && lid_equals l1 l2
  | P_lid l1, P_lid l2 -> lid_equals l1 l2
  | P_inline_for_extraction, P_inline_for_extraction -> true
  | _, _ -> false

let empty_parsing_data = { elts = []; no_prelude = false }

type deps = {
    dep_graph:dependence_graph;                 //dependences of the entire project, not just those reachable from the command line
    file_system_map:files_for_module_name;      //an abstraction of the file system, keys are lowercase module names
    valid_namespaces: SMap.t (list string);     //all namespaces, mapped to the modules in that namespace
    cmd_line_files:list file_name;              //all command-line files
    all_files:ref (RBSet.t file_name);                   //all files
    interfaces_with_inlining:list module_name;  //interfaces that use `inline_for_extraction` require inlining
    parse_results:SMap.t parsing_data             //map from filenames to parsing_data
                                                //callers (Universal.fs) use this to get the parsing data for caching purposes
}
let copy_deps (d:deps) : ML deps = { d with dep_graph = copy_dep_graph d.dep_graph; all_files=mk_ref (!d.all_files) }
let deps_try_find (Deps m) k = SMap.try_find m k
let deps_add_dep (Deps m) k v =
  SMap.add m k v
let deps_keys (Deps m) = SMap.keys m
let deps_empty () = Deps (SMap.create 41)
let mk_deps dg fs ns c a i pr = {
    dep_graph=dg;
    file_system_map=fs;
    valid_namespaces=ns;
    cmd_line_files=c;
    all_files=mk_ref a;
    interfaces_with_inlining=i;
    parse_results=pr;
}
(* In public interface *)
let empty_deps clf = mk_deps (deps_empty ()) (SMap.create 0) (SMap.create 0) clf (RBSet.empty()) [] (SMap.create 0)
let module_name_of_dep = function
    | UseInterface m
    | PreferInterface m
    | UseImplementation m
    | FriendImplementation m -> m

let resolve_module_name (file_system_map:files_for_module_name) (key:module_name)
    : ML (option module_name)
    = match SMap.try_find file_system_map key with
      | Some (Some fn, _)
      | Some (_, Some fn) ->
        Some (lowercase_module_name fn)
      | _ -> None

let interface_of_internal (file_system_map:files_for_module_name) (key:module_name)
: ML (option file_name)
= match SMap.try_find file_system_map key with
  | Some (Some iface, _) -> Some iface
  | _ -> None

let implementation_of_internal (file_system_map:files_for_module_name) (key:module_name)
: ML (option file_name)
= match SMap.try_find file_system_map key with
  | Some (_, Some impl) -> Some impl
  | _ -> None

let has_interface (file_system_map:files_for_module_name) (key:module_name)
    : ML bool =
    Some? (interface_of_internal file_system_map key)

let has_implementation (file_system_map:files_for_module_name) (key:module_name)
    : ML bool =
    Some? (implementation_of_internal file_system_map key)


(*
 * Public interface
 *)
let cache_file_name =
    let checked_file_and_exists_flag fn =
      let mname = fn |> module_name_of_file in
      (* The checked file is named after the module's full (possibly namespaced)
         name rather than the flat basename of [fn]. For a flat source file this
         is a no-op (e.g. [FStar.List.Tot.fst] -> [FStar.List.Tot.fst.checked]),
         but for a hierarchical source such as [A/B/C.fst] it yields
         [A.B.C.fst.checked] instead of [C.fst.checked], so that modules living
         in different namespaces do not collide in the cache directory. We keep
         [fn]'s own extension (e.g. .fst / .fsti) rather than assuming one. *)
      let cache_fn =
        let bn = Filepath.basename fn in
        let ext = match check_and_strip_suffix bn with
                  | Some stem -> Util.substring_from bn (String.length stem)
                  | None ->
                    // Unreachable: [module_name_of_file fn] above would
                    // already have raised Fatal_NotValidFStarFile if [bn]
                    // had no valid F* extension.
                    failwith (Format.fmt1 "Impossible: cache_file_name: file without a valid F* extension: %s" fn) in
        mname ^ ext ^ ".checked"
      in
      match Find.find_file (cache_fn |> Filepath.basename) with
      | Some path ->
        let expected_cache_file = Find.prepend_cache_dir cache_fn in
        if Some? (Options.dep()) //if we're in the dependence analysis
            && not (Options.should_be_already_cached mname) //and checked file is in the
            && (not (Filepath.file_exists expected_cache_file) //wrong spot ... complain
                || not (Filepath.paths_to_same_file path expected_cache_file))
        then (
          let open FStarC.Pprint in
          let open FStarC.Errors.Msg in
          log_issue0 FStarC.Errors.Warning_UnexpectedCheckedFile [
              text "Did not expect module" ^/^ doc_of_string mname ^/^ text "to be already checked.";
              prefix 2 1 (text "Found it in an unexpected location:")
                (doc_of_string path) ^/^
              prefix 2 1 (text "instead of")
                (doc_of_string expected_cache_file);
            ]
        );

        (* This expression morally just returns [path], but prefers
         * the path in [expected_cache_file] is possible to give
         * preference to relative filenames. This is mostly since
         * GNU make doesn't resolve paths in targets, so we try
         * to keep target paths relative. See issue #1978. *)
        if Filepath.file_exists expected_cache_file && Filepath.paths_to_same_file path expected_cache_file
        then expected_cache_file
        else path
      | None ->
        if !dbg_CheckedFiles then
          Format.print1 "find_file(%s) returned None\n" (cache_fn |> Filepath.basename);
        if mname |> Options.should_be_already_cached then
          raise_error0 FStarC.Errors.Error_AlreadyCachedAssertionFailure [
             text (Format.fmt1 "Expected %s to be already checked but could not find it." mname)
           ];
        Find.prepend_cache_dir cache_fn
    in
    let memo = SMap.create 100 in
    let memo (f: string -> ML string) x =
      match SMap.try_find memo x with
      | Some res -> res
      | None ->
        let res = f x in
        SMap.add memo x res;
        res
    in
    memo checked_file_and_exists_flag


let file_of_dep_aux
                (use_checked_file:bool)
                (file_system_map:files_for_module_name)
                (all_cmd_line_files:list file_name)
                (d:dependence)
    : ML file_name =
    // NB: calling this function can be very expensive. It'd be better to
    // precompute an RBSet of the lowercased implementations and just query it
    // here.
    let cmd_line_has_impl key =
        all_cmd_line_files
        |> BU.for_some (fun fn ->
           is_implementation fn && key = lowercase_module_name fn)
    in

    let maybe_use_cache_of f = if use_checked_file then cache_file_name f else f in

    match d with
    | UseInterface key ->
      //This key always resolves to an interface source file
      (match interface_of_internal file_system_map key with
       | None ->
         assert false; //should be unreachable; see the only use of UseInterface in discover_one
         raise_error0 Errors.Fatal_MissingInterface (Format.fmt1 "Expected an interface for module %s, but couldn't find one" key)
       | Some f ->
         f)

    | PreferInterface key //key for module 'a'
        when has_interface file_system_map key ->  //so long as 'a.fsti' exists
      if None? (Options.dep()) // unless we're not just doing a dependency scan using `--dep _`
      && not (fly_deps_enabled ())
         (* In fly_deps mode the "command line" files are really just the roots
            of an incremental scan, and an implementation among them typically
            comes from a `friend` declaration, which is legitimate. *)
      && cmd_line_has_impl key // and the cmd line contains 'a.fst'
      then if Options.expose_interfaces()
           then maybe_use_cache_of (Option.must (implementation_of_internal file_system_map key))
           else raise_error0 Errors.Fatal_MissingExposeInterfacesOption [
                    text <| Format.fmt4 "You may have a cyclic dependence on module %s: use --dep full to confirm. \
                                Alternatively, invoking fstar with %s on the command line breaks \
                                the abstraction imposed by its interface %s.\n
                                all_cmd_line_files=%s\n"
                                key
                                (Option.must (implementation_of_internal file_system_map key))
                                (Option.must (interface_of_internal file_system_map key))
                                (show all_cmd_line_files);
                    text "If you really want this behavior add the option '--expose_interfaces'.";
                  ]
      else maybe_use_cache_of (Option.must (interface_of_internal file_system_map key))   //we prefer to use 'a.fsti'

    | PreferInterface key
    | UseImplementation key
    | FriendImplementation key ->
        match implementation_of_internal file_system_map key with
        | None ->
          //if d is actually an edge in the dep_graph computed by discover
          //then d is only present if either an interface or an implementation exist
          //the previous case already established that the interface doesn't exist
          //     since if the implementation was on the command line, it must exist because of option validation
          raise_error0 Errors.Fatal_MissingImplementation
            (Format.fmt1 "Expected an implementation of module %s, but couldn't find one" key)
        | Some f -> maybe_use_cache_of f

let file_of_dep = file_of_dep_aux false

let files_of_dependences 
      (fn:file_name)
      (file_system_map:files_for_module_name)
      (all_cmd_line_files:list file_name)
      (deps:list dependence)
: ML (list file_name)
= List.map (file_of_dep file_system_map all_cmd_line_files) deps
      |> List.filter (fun k -> k <> fn) (* skip current module, cf #451 *)

let dependences_of (file_system_map:files_for_module_name)
                   (deps:dependence_graph)
                   (all_cmd_line_files:list file_name)
                   (fn:file_name)
    : ML (list file_name) =
    match deps_try_find deps fn with
    | None -> empty_dependences
    | Some ({edges=deps}) -> files_of_dependences fn file_system_map all_cmd_line_files deps

let print_graph (outc : out_channel) (fn : string) (graph:dependence_graph)
  (file_system_map:files_for_module_name)
  (cmd_lined_files:list file_name)
 : ML unit
 =
  if not (Options.silent ()) then begin
    F.print1 "A DOT-format graph has been dumped in the current directory as `%s`\n" fn;
    F.print1 "With GraphViz installed, try: fdp -Tpng -odep.png %s\n" fn;
    F.print1 "Hint: cat %s | grep -v _ | grep -v prims\n" fn
  end;
  let sb = FStarC.StringBuffer.create 10000 in
  let pr str = ignore <| FStarC.StringBuffer.add str sb in
  pr "digraph {\n";
  List.unique (deps_keys graph) |> List.iter (fun k ->
    let deps = (Option.must (deps_try_find graph k)).edges in
    List.iter (fun dep ->
      let l = Filepath.basename k in
      let r = Filepath.basename <| file_of_dep file_system_map cmd_lined_files dep in
      if not <| Options.should_be_already_cached (module_name_of_dep dep) then
        pr (Format.fmt2 "  \"%s\" -> \"%s\"\n" l r)
    ) deps
  );
  pr "}\n";
  fprint outc "%s" [FStarC.StringBuffer.contents sb]

let safe_readdir_for_include (d:string) : ML (list string) =
  try Filepath.readdir d
  with
  | _ -> []

(* Turn a source file [filename] (a basename) into its (long name, path)
   candidate, or [] if it is not a recognized F* source file. [ns_prefix] holds
   the namespace components coming from the directories above it (empty for a
   flat file), and [path] is the path used to locate the file. *)
let module_candidate_of_file (ns_prefix:list string) (path:string) (filename:string)
  : ML (list (string & string)) =
  match check_and_strip_suffix filename with
  | None -> []
  | Some modname -> [(String.concat "." (ns_prefix @ [modname]), path)]

(* Enumerate the (long name, file path) candidates found under a single include
  directory [root], descending into subdirectories and turning each directory
  name into a namespace component: a file at [X/Y/Z.fst] (relative to [root]) is
  mapped to the long name [X.Y.Z]. Directories whose name starts with a '.'
  (e.g. [.git]) are skipped, since they can never be a valid namespace
  component. We also never descend into a subdirectory that is itself an
  include root, so that each include root owns its own traversal. [cwd] is the
  normalized current directory: files under it are reported by their bare path
  relative to [cwd]. *)
let hierarchical_modules_for_dir (cwd:string) (include_roots:list string) (root:string)
  : ML (list (string & string)) =
  let has_include_manifest = Filepath.file_exists (Filepath.join_paths root "fstar.include") in
  (* [ns_prefix] is the list of namespace components corresponding to the
     subdirectories walked so far (in order); [rel] is the path, relative to
     [root], of the directory currently being scanned ("" for [root] itself). *)
  let rec walk (ns_prefix:list string) (rel:string)
    : ML (list (string & string)) =
    let dir = if rel = "" then root else Filepath.join_paths root rel in
    safe_readdir_for_include dir |> List.concatMap (fun entry ->
      let entry = Filepath.basename entry in
      let rel' = if rel = "" then entry else Filepath.join_paths rel entry in
      let entry_path = Filepath.join_paths root rel' in
      if Filepath.is_directory entry_path then
        (* A manifest explicitly selects the child roots to scan; those roots
          are expanded separately by [Find.full_include_path]. *)
        if has_include_manifest
        then []
        (* Never descend into hidden directories (they cannot be namespace
           components). *)
        else if String.length entry > 0 && String.get entry 0 = '.'
        then []
        (* If this directory is itself an include root, let that root's own
           traversal cover it. *)
        else if List.contains entry_path include_roots
        then []
        else walk (ns_prefix @ [entry]) rel'
      else module_candidate_of_file ns_prefix (if root = cwd then rel' else entry_path) entry)
  in
  walk [] ""

(* Build a map from module long name (and interface/implementation role) to the
  file providing it within a single include directory, and check that this map
  is unique: fail hard if any module long name is provided by more than one
  file of the same role. This catches, e.g., a flat [X.Y.Z.fst] and a nested
  [X/Y/Z.fst] both defining module [X.Y.Z], rather than silently picking one.
  Duplicates *across* different include directories remain allowed; later
  directories override earlier ones (see [build_map]). *)
let check_unique_module_names_for_dir (dir:string)
                                      (candidates : list (string & string))
  : ML unit =
  let seen : SMap.t string = SMap.create 100 in
  candidates |> List.iter (fun (longname, path) ->
    let key = String.lowercase longname ^ (if is_interface path then ":i" else ":") in
    match SMap.try_find seen key with
    | Some prev ->
      raise_error0 Errors.Fatal_DuplicateModuleOrInterface [
        text (Format.fmt4 "Module %s is provided by more than one file in include directory %s: %s and %s." longname dir prev path);
        text "A module must have a unique source file. For example, do not provide both a flat 'X.Y.Z.fst' and a nested 'X/Y/Z.fst' for the same module."
      ]
    | None -> SMap.add seen key path)

(** Enumerate all F* files in all include directories, returning a list of pairs
    of long names and full paths.

    We descend into subdirectories, mapping a file at [X/Y/Z.fst] to the long
    name [X.Y.Z] (matching is case-insensitive; long names are lowercased in
    [build_map]).

    We fail hard if any module long name is provided by more than one file of
    the same role within a single include directory (e.g. both a flat
    [X.Y.Z.fst] and a nested [X/Y/Z.fst]). *)
(* In public interface *)
let build_inclusion_candidates_list (): ML (list (string & string)) =
  let include_directories = Find.full_include_path () in
  let include_directories = List.map Filepath.normalize_file_path include_directories in
  (* Note that [BatList.unique] keeps the last occurrence, that way one can
   * always override the precedence order. *)
  let include_directories = List.unique include_directories in
  let cwd = Filepath.normalize_file_path (getcwd ()) in
  include_directories |> List.concatMap (fun d ->
    let candidates = hierarchical_modules_for_dir cwd include_directories d in
    check_unique_module_names_for_dir d candidates;
    candidates)

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to pairs of filenames (/path/to/A.B.fst). Long names are
    all normalized to lowercase. The first component of the pair is the
    interface (if any). The second component of the pair is the implementation
    (if any). *)
let build_map fs_map valid_ns_map (filenames: list string): ML unit =
  let add_fs_entry key full_path =
    match SMap.try_find fs_map key with
    | Some (intf, impl) ->
        if is_interface full_path then
          SMap.add fs_map key (Some full_path, impl)
        else
          SMap.add fs_map key (intf, Some full_path)
    | None ->
        if is_interface full_path then
          SMap.add fs_map key (Some full_path, None)
        else
          SMap.add fs_map key (None, Some full_path)
  in
  let add_ns_entry key full_path =
    match namespace_of_module key with
    | None -> ()
    | Some ns ->
      let ns = Ident.string_of_lid ns in
      match SMap.try_find valid_ns_map ns  with
      | None -> SMap.add valid_ns_map ns [key]
      | Some keys -> SMap.add valid_ns_map ns (key::keys)
  in
  let add_entry key full_path =
    add_fs_entry key full_path;
    add_ns_entry key full_path
  in
  (* Add files from all include directories *)
  List.iter (fun (longname, full_path) ->
    add_entry (String.lowercase longname) full_path
  ) (build_inclusion_candidates_list ());
  (* All the files we've been given on the command-line must be valid FStar files. *)
  List.iter (fun f ->
    add_entry (lowercase_module_name f) f
  ) filenames

let is_valid_namespace deps ns =
  let res = Some? (SMap.try_find deps.valid_namespaces (String.lowercase (Ident.string_of_lid ns))) in
  if not res
  then Format.print2 "Could not resolve namespace %s\n valid namespaces are %s\n"
      (show ns) (show <| List.sortWith String.compare (SMap.keys deps.valid_namespaces));
  res

let interface_of deps key = 
  if Nil? (SMap.keys deps.file_system_map)
  then build_map deps.file_system_map deps.valid_namespaces deps.cmd_line_files;
  interface_of_internal deps.file_system_map key
let implementation_of deps key =
  if Nil? (SMap.keys deps.file_system_map)
  then build_map deps.file_system_map deps.valid_namespaces deps.cmd_line_files;
  implementation_of_internal deps.file_system_map key

let string_of_lid (l: lident) (last: bool) =
  let suffix = if last then [ (string_of_id (ident_of_lid l)) ] else [ ] in
  let names = List.map (fun x -> (string_of_id x)) (ns_of_lid l) @ suffix in
  String.concat "." names

(** All the components of a [lident] joined by "." (the last component of the
 * lident is included iff [last = true]).  *)
let lowercase_join_longident (l: lident) (last: bool) =
  String.lowercase (string_of_lid l last)

let namespace_of_lid l =
  String.concat "_" (List.map string_of_id (ns_of_lid l))

let check_module_declaration_against_filename (lid: lident) (filename: string): ML unit =
  let k' = string_of_lid lid true in
  if Option.must (check_and_strip_suffix (Filepath.basename filename)) <> k' then
    log_issue lid Errors.Error_ModuleFileNameMismatch [
        Errors.Msg.text (Format.fmt2 "The module declaration \"module %s\" \
          found in file %s does not match its filename." (string_of_lid lid true) filename);
        Errors.Msg.text "Dependencies will be incorrect and the module will not be verified.";
      ]

exception Exit

let dep_subsumed_by d d' =
      match d, d' with
      | PreferInterface l', FriendImplementation l -> l=l'
      | _ -> d = d'

let warned_about : ref (list (option intf_and_impl)) = mk_ref Nil

(** For all items [i] in the map that start with [prefix], add an additional
    entry where [i] stripped from [prefix] points to the same value. Returns a
    boolean telling whether the map was modified.

    If the open is an implicit open (as indicated by the flag),
    and doing so shadows an existing entry, warn! *)
(* [enter_namespace] shortens every module under [sprefix] into [working_map],
   and used to do so by scanning the whole module map and recomputing, for each
   hit, the suffix, the file it maps to and whether that suffix shadows an
   existing module.  All of that depends only on [original_map], while
   [enter_namespace] is called several times per file for a few hundred files,
   so it is precomputed once here, indexed by dot-terminated prefix.

   The index is memoized on the map itself: [build_map] only ever populates a
   map that is still empty (see [interface_of]), so a non-empty map is never
   mutated again.  Buckets are built by prepending during [SMap.iter] and then
   reversed, so iterating a bucket visits entries in exactly the order
   [SMap.iter] used to, keeping the order of the shadowing warnings unchanged. *)
type ns_entry = {
  ne_suffix   : string;            //the shortened name
  ne_file     : intf_and_impl;     //what it resolves to
  ne_shadowed : option intf_and_impl; //the module this shortening shadows, if any
}

let ns_index_memo : ref (option (files_for_module_name & SMap.t (list ns_entry))) =
  mk_ref None

let namespace_index (m:files_for_module_name) : ML (SMap.t (list ns_entry)) =
  match !ns_index_memo with
  | Some (m', idx) when BU.physical_equality m m' -> idx
  | _ ->
    let idx : SMap.t (list ns_entry) = SMap.create 100 in
    let suffix_exists mopt =
      match mopt with
      | None -> false
      | Some (intf, impl) -> Some? intf || Some? impl
    in
    SMap.iter m (fun k fn ->
      (* register [k] under each of its proper dot-terminated prefixes:
         "a.b.c" is registered under "a." as "b.c" and under "a.b." as "c" *)
      let rec prefixes (acc:string) (segs:list string) : ML unit =
        match segs with
        | [] | [_] -> ()
        | seg :: rest ->
          let p = acc ^ seg ^ "." in
          let suffix =
            String.substring k (String.length p) (String.length k - String.length p)
          in
          let shadowed =
            let so = SMap.try_find m suffix in
            if suffix_exists so then so else None
          in
          let e = { ne_suffix = suffix; ne_file = fn; ne_shadowed = shadowed } in
          let cur = match SMap.try_find idx p with None -> [] | Some l -> l in
          SMap.add idx p (e :: cur);
          prefixes p rest
      in
      prefixes "" (String.split ['.'] k)
    );
    SMap.keys idx |> List.iter (fun p ->
      SMap.add idx p (List.rev (Option.must (SMap.try_find idx p)))
    );
    ns_index_memo := Some (m, idx);
    idx

let enter_namespace
  (original_map: files_for_module_name)
  (working_map: files_for_module_name)
  (sprefix: string)
  (implicit_open:bool) : ML bool =
  let sprefix = sprefix ^ "." in
  let entries =
    match SMap.try_find (namespace_index original_map) sprefix with
    | None -> []
    | Some l -> l
  in
  entries |> List.iter (fun e ->
    (match e.ne_shadowed with
     | Some _ when implicit_open && not (List.mem e.ne_shadowed !warned_about) ->
       let str = e.ne_shadowed |> Option.must |> intf_and_impl_to_string in
       warned_about := e.ne_shadowed :: !warned_about;
       let open FStarC.Pprint in
       log_issue0 Errors.Warning_UnexpectedFile [
          flow (break_ 1) [
            text "Implicitly opening namespace";
            fquotes (doc_of_string sprefix);
            text "shadows module";
            fquotes (doc_of_string e.ne_suffix);
            text "in file";
            fquotes (doc_of_string str) ^^ dot;
          ];
          text "Rename" ^/^ fquotes (doc_of_string str) ^/^ text "to avoid conflicts.";
       ]
     | _ -> ());
    SMap.add working_map e.ne_suffix e.ne_file
  );
  Cons? entries

let prelude_lid = Ident.lid_of_str "FStar.Prelude"
let prelude : list (open_kind & lid) = [
   (Open_namespace, Const.fstar_ns_lid);
   (Open_module,    prelude_lid);
]

//For --ide mode, we stop dependence analysis at interface boundaries
//and do not check for dependence cycles across interface boundaries
let peek_past_interfaces () =
  if Options.Ext.enabled "dep_minimal"|| fly_deps_enabled()
  then false
  else not (Options.ide ())

let collect_module_or_decls (filename:string) (m:either modul (list decl)) : ML parsing_data =
  //parse the file and traverse the AST to collect parsing data
  let num_of_toplevelmods = mk_ref 0 in
  let pd : ref parsing_data = mk_ref empty_parsing_data in

  let add_to_parsing_data elt =
    if not (List.existsML (fun e -> parsing_data_elt_eq e elt) (!pd).elts)
    then pd := { !pd with elts = elt::(!pd).elts }
  in

  let set_no_prelude b =
    pd := { !pd with no_prelude = b }
  in

  let rec go (x: either modul (list decl)) : ML unit = match x with
    | Inl (Module {no_prelude; mname; decls})
    | Inl (Interface {no_prelude; mname; decls}) ->
        set_no_prelude no_prelude;
        // check_module_declaration_against_filename mname filename;
        add_to_parsing_data (P_begin_module mname);
        collect_decls decls
    | Inr decls ->
        set_no_prelude true;
        collect_decls decls

  and collect_decls (decls: list decl) : ML unit =
    List.iter (fun x -> collect_decl x.d;
                        List.iter collect_term x.attrs;
                        match x.d with
                        | _ when List.contains Inline_for_extraction x.quals ->
                            add_to_parsing_data P_inline_for_extraction
                        | _ -> ()
                        ) decls

  and collect_decl (d: decl') : ML unit =
    match d with
    | Include (lid, _)
    | Open (lid, _) ->
        add_to_parsing_data (P_open (false, lid))
    | Friend lid ->
        add_to_parsing_data (P_dep (true, (lowercase_join_longident lid true |> Ident.lid_of_str)))
    | ModuleAbbrev (ident, lid) ->
        add_to_parsing_data (P_alias (ident, lid))
    | TopLevelLet (_, patterms) ->
        List.iter (fun (pat, t) -> collect_pattern pat; collect_term t) patterms
    | Splice (_, _, t)
    | Assume (_, t)
    | Val (_, t) ->
        collect_term t
    | SubEffect _ -> ()
    | Tycon (_, tc, ts) ->
        begin
        if tc then
            add_to_parsing_data (P_lid Const.tcclass_lid);
        List.iter collect_tycon ts
        end
    | Exception (_, t) ->
        Option.iter collect_term t
    | NewEffect ed ->
          collect_effect_decl ed

    | DeclToBeDesugared tbs ->
        tbs.dep_scan 
        { scan_term = collect_term;
          scan_binder = collect_binder;
          scan_pattern = collect_pattern;
          add_lident = (fun lid -> add_to_parsing_data (P_lid lid));
          add_open = (fun lid -> add_to_parsing_data (P_open (true, lid)))
        }
        tbs.blob

    | UseLangDecls _
    | Pragma _
    | DeclSyntaxExtension _
    | Unparseable ->
        ()
    | TopLevelModule lid ->
        incr num_of_toplevelmods;
        if (!num_of_toplevelmods > 1) then
          raise_error lid Errors.Fatal_OneModulePerFile
            (Format.fmt1 "Automatic dependency analysis demands one module per file (module %s not supported)" (string_of_lid lid true)) 
  and collect_tycon (tc: tycon) : ML unit = match tc with
    | TyconAbstract (_, binders, k) ->
        collect_binders binders;
        Option.iter collect_term k
    | TyconAbbrev (_, binders, k, t) ->
        collect_binders binders;
        Option.iter collect_term k;
        collect_term t
    | TyconRecord (_, binders, k, _, identterms) ->
        collect_binders binders;
        Option.iter collect_term k;
        collect_tycon_record identterms
    | TyconVariant (_, binders, k, identterms) ->
        collect_binders binders;
        Option.iter collect_term k;
        List.iter ( function
                  | VpOfNotation t | VpArbitrary t -> collect_term t
                  | VpRecord (record, t) -> collect_tycon_record record;
                                            Option.iter collect_term t
                  ) (List.filter_map Mktuple3?._2 identterms)

  and collect_tycon_record (r: list (ident & aqual & attributes_ & term)) : ML unit =
    List.iter (fun (_, aq, attrs, t) ->
            collect_aqual aq;
            attrs |> List.iter collect_term;
            collect_term t) r

  and collect_effect_decl (ed: effect_decl) : ML unit = match ed with
    | DeclareEffect (_, binders) ->
        collect_binders binders
    | DefineEffect (_, binders, decls) ->
        collect_binders binders;
        List.iter (fun d -> collect_decl d.d) decls
    | RedefineEffect (_, binders, t) ->
        collect_binders binders;
        collect_term t

  and collect_binders (binders: list binder) : ML unit =
    List.iter collect_binder binders

  and collect_binder (b: binder) : ML unit =
    collect_aqual b.aqual;
    b.battributes |> List.iter collect_term;
    match b with
    | { b = Annotated (_, t) }
    | { b = NoName t } -> collect_term t
    | _ -> ()

  and collect_aqual (aq: aqual) : ML unit = match aq with
    | Some (Meta t) -> collect_term t
    | Some TypeClassArg -> add_to_parsing_data (P_lid Const.tcresolve_lid)
    | _ -> ()

  and collect_term (t: term) : ML unit =
    collect_term' t.tm

  and collect_constant (c: sconst) : ML unit = match c with
    | Const_int (_, Some (Unsigned, Sizet)) ->
        add_to_parsing_data (P_dep (false, ("fstar.sizeT" |> Ident.lid_of_str)))
    | Const_int (_, Some (signedness, width)) ->
        let u = match signedness with | Unsigned -> "u" | Signed -> "" in
        let w = match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64" in
        add_to_parsing_data (P_dep (false, (Format.fmt2 "fstar.%sint%s" u w |> Ident.lid_of_str)))
    | Const_char _ ->
        add_to_parsing_data (P_dep (false, ("fstar.char" |> Ident.lid_of_str)))
    | Const_range_of
    | Const_set_range_of ->
        add_to_parsing_data (P_dep (false, ("fstar.range" |> Ident.lid_of_str)))
    | Const_real _ ->
        (* FStar.Real has a real literal it, don't add a circular dep. *)
        let mm = maybe_module_name_of_file filename in
        if mm <> Some "FStar.Real" then
          add_to_parsing_data (P_dep (false, ("fstar.real" |> Ident.lid_of_str)))
    | _ ->
        ()

  and collect_term' (t: term') : ML unit = match t with
    | Wild ->
        ()
    | Const c ->
        collect_constant c
    | Op (_, ts) ->
        List.iter collect_term ts
    | AST.Uvar _ ->
        ()
    | Var lid
    | AST.Projector (lid, _)
    | AST.Discrim lid
    | Name lid ->
        add_to_parsing_data (P_lid lid)
    | Construct (lid, termimps) ->
        add_to_parsing_data (P_lid lid);
        List.iter (fun (t, _) -> collect_term t) termimps
    | Function (branches, _) ->
      collect_branches branches
    | Abs (pats, t) ->
        collect_patterns pats;
        collect_term t
    | App (t1, t2, _) ->
        collect_term t1;
        collect_term t2
    | Let (_, patterms, t) ->
        List.iter (fun (attrs_opt, (pat, t)) ->
            ignore (Option.map (List.iter collect_term) attrs_opt);
            collect_pattern pat;
            collect_term t)
            patterms;
        collect_term t
    | LetOperator (lets, body) ->
        List.iter (fun (ident, pat, def) ->
            collect_pattern pat;
            collect_term def
        ) lets;
        collect_term body
    | LetOpen (lid, t) ->
        add_to_parsing_data (P_open (true, lid));
        collect_term t
    | LetOpenRecord (r, rty, e) ->
        collect_term r;
        collect_term rty;
        collect_term e
    | Bind(_, t1, t2)
    | Seq (t1, t2) ->
        collect_term t1;
        collect_term t2
    | If (t1, _, ret_opt, t2, t3) ->
        collect_term t1;
        (match ret_opt with
          | None -> ()
          | Some (_, ret, _) ->
            collect_term ret);
        collect_term t2;
        collect_term t3
    | Match (t, _, ret_opt, bs) ->
        collect_term t;
        (match ret_opt with
          | None -> ()
          | Some (_, ret, _) ->
            collect_term ret);
        collect_branches bs
    | TryWith (t, bs) ->
        collect_term t;
        collect_branches bs
    | Ascribed (t1, t2, None, _) ->
        collect_term t1;
        collect_term t2
    | Ascribed (t1, t2, Some tac, _) ->
        collect_term t1;
        collect_term t2;
        collect_term tac
    | Record (t, idterms) ->
        Option.iter collect_term t;
        List.iter
          (fun (fn, t) ->
            collect_fieldname fn;
            collect_term t)
          idterms
    | Project (t, f) ->
        collect_term t;
        collect_fieldname f
    | Product (binders, t) ->
      collect_binders binders;
      collect_term t
    | Sum (binders, t) ->
        List.iter (function
          | Inl b -> collect_binder b
          | Inr t -> collect_term t)
          binders;
        collect_term t
    | QForall (binders, (_, ts), t)
    | QExists (binders, (_, ts), t)
    | QuantOp (_, binders, (_, ts), t) ->
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
    | Requires t
    | Ensures t
    | Labeled (t, _, _) ->
        collect_term t
    | LexList l -> List.iter collect_term l
    | WFOrder (t1, t2) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.WellFounded")));
      begin
        collect_term t1; collect_term t2
      end
    | Decreases t -> collect_term t
    | Quote (t, _)
    | Antiquote t
    | VQuote t ->
        collect_term t
    | Attributes cattributes  ->
        List.iter collect_term cattributes
    | CalcProof (rel, init, steps) ->
        add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Calc")));
        begin
        collect_term rel;
        collect_term init;
        List.iter (function CalcStep (rel, just, next) ->
            collect_term rel;
            collect_term just;
            collect_term next) steps
        end

    | IntroForall (bs, p, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_binders bs;
      collect_term p;
      collect_term e

    | IntroExists(bs, t, vs, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_binders bs;
      collect_term t;
      List.iter collect_term vs;
      collect_term e

    | IntroImplies(p, q, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term e

    | IntroOr(b, p, q, r) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term r

    | IntroAnd(p, q, r, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term r;
      collect_term e

    | ElimForall(bs, p, vs) ->
        add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
        collect_binders bs;
        collect_term p;
        List.iter collect_term vs

    | ElimExists(bs, p, e) ->
        add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
        collect_binders bs;
        collect_term p;
        collect_term e

    | ElimImplies(p, q, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term e

    | ElimAnd(p, q, e) ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term e

    | ElimOr(p, q, e, e') ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
      collect_term p;
      collect_term q;
      collect_term e;
      collect_term e'

    | ListLiteral ts ->
      List.iter collect_term ts

    | SeqLiteral ts ->
      add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Seq.Base")));
      List.iter collect_term ts
    
  and collect_patterns (ps: list pattern) : ML unit =
    List.iter collect_pattern ps

  and collect_pattern (p: pattern) : ML unit =
    collect_pattern' p.pat

  and collect_pattern' (p: pattern') : ML unit = match p with
    | PatVar (_, aqual, attrs)
    | PatWild (aqual, attrs) ->
        collect_aqual aqual;
        attrs |> List.iter collect_term

    | PatRest
    | PatOp _
    | PatConst _ ->
        ()
    | PatVQuote t ->
        collect_term t
    | PatApp (p, ps) ->
        collect_pattern p;
        collect_patterns ps
    | PatName lid ->
        add_to_parsing_data (P_lid lid)
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


  and collect_branches (bs: list branch) : ML unit =
    List.iter collect_branch bs

  and collect_branch (b: branch) : ML unit =
    let (pat, t1, t2) = b in
    collect_pattern pat;
    Option.iter collect_term t1;
    collect_term t2

  and collect_fieldname (fn: lident) : ML unit =
      if nsstr fn <> ""
      then add_to_parsing_data (P_dep (false, lid_of_ids (ns_of_lid fn)))
  in
  go m;
  !pd

let maybe_use_interface file_system_map file_name =
   let module_name = lowercase_module_name file_name in
    if is_implementation file_name
    && has_interface file_system_map module_name
    then [UseInterface module_name]
    else []

(*
  * Construct dependences from the parsing data
  * This is common function for when the parsing data is read from the checked files
  *   or constructed after AST traversal of the module
  *)
let deps_from_parsing_data (pd:parsing_data) (original_map:files_for_module_name) (filename:string)
: ML (list dependence & //direct dependences
  bool &            //has inline for extraction
  list dependence)   //additional roots
= 
  let deps     : ref (list dependence) = mk_ref [] in
  let has_inline_for_extraction = mk_ref false in

  let mname = lowercase_module_name filename in
  let mo_roots =
    if is_interface filename
    && has_implementation original_map mname
    && peek_past_interfaces()
    then [ UseImplementation mname ]
    else []
  in

  let auto_open =
    let open_module_ns =
      (match namespace_of_module mname with
        | None -> []
        | Some ns -> [ P_implicit_open_module_or_namespace (Open_namespace, ns) ])
    in
    if pd.no_prelude
    then open_module_ns
    else
      (prelude |> List.map (fun (k, l) -> P_open (false, l)))
      @open_module_ns
  in

  let working_map = SMap.copy original_map in

  let set_interface_inlining () =
    if is_interface filename
    then has_inline_for_extraction := true
  in

  let add_dep d =
    if not (List.existsML (dep_subsumed_by d) !deps) then (
      deps := d :: !deps
    )
  in

  let dep_edge module_name is_friend =
    if is_friend then FriendImplementation module_name
    else PreferInterface module_name
  in

  let add_dependence_edge original_or_working_map lid is_friend =
    let key = lowercase_join_longident lid true in
    if !dbg then Format.print1 "Resolving %s ..\n" key;
    match resolve_module_name original_or_working_map key with
    | Some module_name ->
      if is_friend
      && fly_deps_enabled()
      then (
        let already_depends_on_iface =
          !deps 
          |> List.existsb (function
              | PreferInterface mname' -> mname' = mname
              | _ -> false)
        in
        if already_depends_on_iface then
           raise_error (range_of_lid lid) Errors.Fatal_CyclicDependence [
            text "Friend dependences must be declared as the first dependence on a module.";
            text (Format.fmt1 "A non-friend dependence was already found on module %s." module_name)
          ]
      
      );
      add_dep (dep_edge module_name is_friend);
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
    if (let_open     && add_dependence_edge working_map lid false)
    || (not let_open && add_dependence_edge original_map lid false)
    then true
    else begin
      if let_open then
        log_issue lid Errors.Warning_ModuleOrFileNotFoundWarning
          (Format.fmt1 "Module not found: %s" (string_of_lid lid true));
      false
    end
  in

  let record_open_namespace lid (implicit_open:bool) =
    let key = lowercase_join_longident lid true in
    let r = enter_namespace original_map working_map key implicit_open in
    if not r && not implicit_open then  //suppress the warning for implicit opens
      log_issue lid Errors.Warning_ModuleOrFileNotFoundWarning
        (Format.fmt1 "No modules in namespace %s and no file with that name either" (string_of_lid lid true))
  in

  let record_open let_open lid =
    if record_open_module let_open lid
    then ()
    else if not let_open //syntactically, this cannot be a namespace if let_open is true; so don't retry
    then record_open_namespace lid false
  in

  let record_implicit_open_module_or_namespace (lid, kind) =
    match kind with
    | Open_namespace -> record_open_namespace lid true
    | Open_module -> let _ = record_open_module false lid in ()
  in

  let record_module_alias ident lid =
    let key = String.lowercase (string_of_id ident) in
    let alias = lowercase_join_longident lid true in
    // Only fully qualified module aliases are allowed.
    match SMap.try_find original_map alias with
    | Some deps_of_aliased_module ->
      SMap.add working_map key deps_of_aliased_module;
      add_dep (dep_edge (lowercase_join_longident lid true) false);
      true
    | None ->
      log_issue lid Errors.Warning_ModuleOrFileNotFoundWarning
        (Format.fmt1 "module not found in search path: %s" alias);
      false
  in

  let add_dep_on_module (module_name : lid) (is_friend : bool) =
    if !dbg then
      Format.print1 "Adding dep on module %s ..\n" (show module_name);
    if add_dependence_edge working_map module_name is_friend
    then ()
    else if !dbg then
      log_issue module_name Errors.Warning_UnboundModuleReference
        (Format.fmt1 "Unbound module reference %s" (show module_name))
  in

  let record_lid lid =
    (* Thanks to the new `?.` and `.(` syntaxes, `lid` is no longer a
      module name itself, so only its namespace part is to be
      recorded as a module dependency.  *)
    match ns_of_lid lid with
    | [] -> ()
    | ns ->
      let module_name = Ident.lid_of_ids ns in
      add_dep_on_module module_name false
  in

  let begin_module lid =
    if Cons? (ns_of_lid lid) then (
      if !dbg then Format.print1 "Begin module %s ..\n" (show lid);
      ignore (enter_namespace original_map working_map (String.lowercase (namespace_of_lid lid)))
    )
  in

  (*
  * Iterate over the parsing data elements
  *)
  let elts =
    if fly_deps_enabled ()
    && pd.no_prelude
    then
      match pd.elts with
      | P_open (false, fstar_lid)::P_open(false, prelude_lid')::rest 
        when
          Ident.lid_equals Const.fstar_ns_lid fstar_lid &&
          Ident.lid_equals prelude_lid prelude_lid' ->
        P_open (false, fstar_lid)::P_open(false, prelude_lid)::auto_open@rest
      | _ -> auto_open@pd.elts
    else auto_open @ pd.elts
  in
  begin
    elts |> List.iter (fun elt ->
      match elt with
      | P_begin_module lid -> begin_module lid
      | P_open (b, lid) -> record_open b lid
      | P_implicit_open_module_or_namespace (k, lid) -> 
        if !dbg then Format.print1 "Implicitly opening %s ..\n" (show lid);
        record_implicit_open_module_or_namespace (lid, k)
      | P_dep (b, lid) -> add_dep_on_module lid b
      | P_alias (id, lid) -> ignore (record_module_alias id lid)
      | P_lid lid -> record_lid lid
      | P_inline_for_extraction -> set_interface_inlining ())
  end;
  (*
  * And then return the dependences
  *)
  !deps,
  !has_inline_for_extraction,
  mo_roots


(*
 * Get parsing data for a file
 * First see if the data in the checked file is good (using the provided callback)
 * If it is, return that
 *
 * Else parse the file, walk its AST, return a list of FStar lowercased module names
    it depends on
 *)

let collect_one
  (original_map: files_for_module_name)
  (filename: string)
  (get_parsing_data_from_cache:string -> ML (option parsing_data))
  : ML (parsing_data &
    list dependence &  //direct dependence
    bool &  //has_inline_for_extraction
    list dependence)  //additional roots
                      //that used to be part of parsing_data earlier
                      //removing it from the cache (#1657)
                      //this always returns a single element, remove the list?
=
  let data_from_cache = filename |> get_parsing_data_from_cache in
  if data_from_cache |> Some? then begin  //we found the parsing data in the checked file
    let deps, has_inline_for_extraction, mo_roots =
      deps_from_parsing_data (data_from_cache |> Option.must) original_map filename
    in
    if !dbg then
      Format.print2 "Reading the parsing data for %s from its checked file .. found %s\n" filename (show deps);
    data_from_cache |> Option.must,
    deps, has_inline_for_extraction, mo_roots
  end
  else begin
      let ast, _ = Driver.parse_file filename in
      let pd = collect_module_or_decls filename (Inl ast) in
      let pd = { pd with elts = List.rev pd.elts } in
      if !dbg then Format.print2 "Parsing data of %s: %s\n" filename (show pd);
      let deps, has_inline_for_extraction, mo_roots = deps_from_parsing_data pd original_map filename in
      if !dbg then Format.print2 "Deps for %s: %s\n" filename (show deps);
      pd, deps, has_inline_for_extraction, mo_roots
    end


(* JP: it looks like the code was changed but the comments were never updated.
 * In particular, we no longer compute transitive dependencies, and we no longer
 * map lowercase module names to filenames. *)

// Used by F*.js
let collect_one_cache : ref (SMap.t (list dependence & list dependence & bool)) =
  mk_ref (SMap.create 0)

let set_collect_one_cache (cache: SMap.t (list dependence & list dependence & bool)) : ML unit =
  collect_one_cache := cache

let dep_graph_copy dep_graph =
    let (Deps g) = dep_graph in
    Deps (SMap.copy g)

let widen_deps friends dep_graph file_system_map widened =
    let widened = mk_ref widened in
    let (Deps dg) = dep_graph in
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
    SMap.fold
       dg
       (fun filename dep_node () ->
          SMap.add
            dg'
            filename
            ({dep_node with edges=widen_one dep_node.edges; color=White}))
       ();
    !widened, Deps dg'

let topological_dependences_of'
        file_system_map
        dep_graph
        interfaces_needing_inlining
        root_files
        widened
    : ML (list file_name
    & bool) =
    let rec all_friend_deps_1
            dep_graph
            (cycle:list file_name)
            (acc: list module_name & list string)
            filename
    : ML _ =
    let (all_friends, all_files) = acc in
    let dep_node = Option.must (deps_try_find dep_graph filename) in
    match dep_node.color with
    | Gray ->
        failwith "Impossible: cycle detected after cycle detection has passed"
    | Black ->
        (* If the element has been visited already, then the map contains all its
            * dependencies. Otherwise, the map only contains its direct dependencies. *)
        all_friends, all_files
    | White ->
        if !dbg
        then Format.print2 "Visiting %s: direct deps are %s\n"
                filename (show dep_node.edges);
        (* Unvisited. Compute. *)
        deps_add_dep dep_graph filename ({dep_node with color=Gray});
        let all_friends, all_files =
            all_friend_deps
                dep_graph cycle (all_friends, all_files)
                (dependences_of file_system_map
                                dep_graph
                                root_files
                                filename)
        in
        (* Mutate the graph to mark the node as visited *)
        deps_add_dep dep_graph filename ({dep_node with color=Black});
        if !dbg
        then Format.print1 "Adding %s\n" filename;
        (* Also build the topological sort (Tarjan's algorithm). *)
        List.collect
          (function | FriendImplementation m -> [m]
                    | d -> [])
         dep_node.edges
        @all_friends,
        filename :: all_files
    and all_friend_deps dep_graph cycle all_friends filenames : ML _ =
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
    let friends, all_files_0 =
        all_friend_deps dep_graph [] ([], []) root_files
    in
    if !dbg
    then Format.print3 "Phase1 complete:\n\t\
                       all_files = %s\n\t\
                       all_friends=%s\n\t\
                       interfaces_with_inlining=%s\n"
                   (String.concat ", " all_files_0)
                   (String.concat ", " (remove_dups_fast friends))
                   (String.concat ", " (interfaces_needing_inlining));
    if fly_deps_enabled() //no need to widen; we enforce that friends are first deps
    then all_files_0, false
    else begin
      match friends with
      | [] -> all_files_0, false
      | _ -> 
        let widened, dep_graph = widen_deps friends dep_graph file_system_map widened in
        let _, all_files =
          if !dbg
          then Format.print_string "==============Phase2==================\n";
          all_friend_deps dep_graph [] ([], []) root_files
        in
        if !dbg
        then Format.print1 "Phase2 complete: all_files = %s\n" (String.concat ", " all_files);
        all_files,
        widened
    end

let phase1
        file_system_map
        dep_graph
        interfaces_needing_inlining
        for_extraction
=
    if !dbg
    then Format.print_string "==============Phase1==================\n";
    let widened = false in
    if Options.cmi()
    && for_extraction
    then widen_deps interfaces_needing_inlining dep_graph file_system_map widened
    else widened, dep_graph

let topological_dependences_of
        file_system_map
        dep_graph
        interfaces_needing_inlining
        root_files
        for_extraction
    : ML (list file_name
    & bool) =

    let widened, dep_graph = phase1 file_system_map dep_graph interfaces_needing_inlining for_extraction in
    topological_dependences_of' file_system_map dep_graph interfaces_needing_inlining root_files widened

let all_files_in_include_paths () =
  let paths = Find.full_include_path () in
  List.collect
    (fun path -> 
      let files = safe_readdir_for_include path in
      let files = List.filter (fun f -> List.existsb (fun ext -> Util.ends_with f ext) (all_file_suffixes ())) files in
      List.map (fun file -> Filepath.join_paths path file) files)
    paths

let build_dep_graph_for_files
      (files:list string)
      (all_cmd_line_files:list string)
      (file_system_map:_)
      (dep_graph:_)
      (parse_results:_)
      (get_parsing_data_from_cache:string -> ML (option parsing_data))
: ML (list string) //interfaces needing inlining
= (* The dependency graph; keys are lowercased module names, values = list of
   * lowercased module names this file depends on. *)
  let interfaces_needing_inlining = mk_ref [] in
  let add_interface_for_inlining l =
    let l = lowercase_module_name l in
    interfaces_needing_inlining := l :: !interfaces_needing_inlining
  in
  (* discover: Do a graph traversal starting from file_name
   *           filling in dep_graph with the dependences *)
  let rec discover_one (file_name:file_name) : ML unit =
    if deps_try_find dep_graph file_name = None then
    begin
      let parsing_data, (deps, mo_roots, needs_interface_inlining) =
        match SMap.try_find !collect_one_cache file_name with
        | Some cached ->
          debug_print (fun _ -> 
            Format.print1 "Using cached parsing data for %s\n" file_name
          );
          empty_parsing_data, cached
        | None ->
          let parsing_data, deps, needs_interface_inlining, additional_roots =
            collect_one file_system_map file_name get_parsing_data_from_cache
          in
          parsing_data, (deps, additional_roots, needs_interface_inlining)
      in
      debug_print (fun _ -> 
        Format.print3 "collect_one (%s) : deps=%s; mo_roots=%s\n"
          file_name (show deps) (show mo_roots)
      );
      if needs_interface_inlining
      then add_interface_for_inlining file_name;
      SMap.add parse_results file_name parsing_data;
      let deps = deps @ maybe_use_interface file_system_map file_name in
      let dep_node : dep_node = {
        edges = List.unique deps;
        color = White;
      } in
      deps_add_dep dep_graph file_name dep_node;
      List.iter
            discover_one
            (List.map (file_of_dep file_system_map all_cmd_line_files)
                      (deps @ mo_roots))
    end
  in
  profile (fun () -> List.iter discover_one files) "FStarC.Parser.Dep.discover"; 
  !interfaces_needing_inlining


let root_friends : ref (list lident) = mk_ref []
let set_root_friends (ls:list lident) : ML unit = root_friends := ls

let collect_deps_of_decl (deps:deps) (filename:string) (ds:list decl)
  (scope_pds: list parsing_data_elt)
  (get_parsing_data_from_cache:string -> ML (option parsing_data))
: ML (list file_name)
= let roots =
    match ds with
    | {d=TopLevelModule l; attrs}::_ -> 
      if !dbg then 
        Format.print2 "Top-level module %s with attrs=%s\n"
            (show l)
            (show attrs);
      let no_prelude =
        Options.no_prelude () || (* only affects current module *)
        attrs |> List.existsb (function t ->
          match t.tm with
          | Const (FStarC.Const.Const_string ("no_prelude", _)) -> true
          | _ -> false)
      in
      Inl <| Parser.AST.Module { mname = l; decls = ds; no_prelude }
   | _ -> Inr ds
  in
  if Nil? (SMap.keys deps.file_system_map)
  then build_map deps.file_system_map deps.valid_namespaces [filename];
  let pd = collect_module_or_decls filename roots in
  debug_print (fun _ -> 
    Format.print2 "Got pds=%s and scope_pds=%s\n" (show pd.elts) (show scope_pds));
  (* Scanning the module header of an implementation makes its own interface a
     dependence: the interface's checked sigelts seed the to-do list against
     which the implementation is checked. The interface may itself depend on
     modules that the implementation befriends, and a friend dependence has to
     be the first dependence on a module; so the whole file is scanned for
     [friend] declarations here, even though only the header is being processed. *)
  let own_interface, own_friends =
    match ds with
    | {d=TopLevelModule _}::_ when is_implementation filename -> (
      match interface_of_internal deps.file_system_map (lowercase_module_name filename) with
      | None -> None, []
      | Some iface ->
        let ast, _ = Driver.parse_file filename in
        let friends =
          decls_of_modul ast |> List.collect (fun d ->
            match d.d with
            | Friend lid -> [P_dep (true, (lowercase_join_longident lid true |> Ident.lid_of_str))]
            | _ -> [])
        in
        Some iface, friends
    )
    | _ -> None, []
  in
  let pd = { pd with elts = List.map (fun l -> P_dep (true, l)) !root_friends
                             @ own_friends
                             @ List.rev scope_pds@List.rev pd.elts } in
  let direct_deps, _has_inline_for_extraction, _additional_roots = deps_from_parsing_data pd deps.file_system_map filename in
  debug_print (fun _ ->
     Format.print3 "direct deps of %s is %s, mo_roots=%s\n" 
      (show ds) (show direct_deps) (show _additional_roots)); 
  let files = List.map (file_of_dep deps.file_system_map []) direct_deps in
  let files =
    match own_interface with
    | None -> files
    | Some iface -> files @ [iface]
  in
  let inline_ifaces = build_dep_graph_for_files files [] deps.file_system_map deps.dep_graph deps.parse_results get_parsing_data_from_cache in
  let filenames, _ = topological_dependences_of deps.file_system_map deps.dep_graph inline_ifaces files false in
  deps.all_files := RBSet.union (!deps.all_files) (RBSet.from_list filenames);
  filenames

(** Collect the dependencies for a list of given files.
    And record the entire dependence graph in the memoized state above **)
(*
 * get_parsing_data_from_cache is a callback passed by caller
 *   to read the parsing data from checked files
 *)

(** Find all F* files in a directory, respecting fstar.include for subdirectory traversal.
    Uses Find.expand_include_d to determine which subdirectories to visit. *)
let all_fstar_files_in_dir (dir:string) : ML (list file_name) =
  let dirs = Find.expand_include_d dir in
  List.collect (fun d ->
    let files = safe_readdir_for_include d in
    List.collect (fun f ->
      let full_path = Filepath.join_paths d f in
      if not (Filepath.is_directory full_path)
        && List.existsb (fun ext -> Util.ends_with f ext) (all_file_suffixes ())
      then [full_path]
      else []
    ) files
  ) dirs

(** Expand any directories in the command line file list to their contained F* files. *)
let expand_directories (files: list file_name) : ML (list file_name) =
  files |> List.collect (fun f ->
    if Filepath.is_directory f then
      all_fstar_files_in_dir f
    else
      [f]
  )

(* In public interface *)
let collect (all_cmd_line_files: list file_name)
            (get_parsing_data_from_cache:string -> ML (option parsing_data))
    : ML (list file_name
    & deps) //topologically sorted transitive dependences of all_cmd_line_files
    =
  Stats.record "Parser.Dep.collect" fun () ->
  (* Expand any directories to their contained F* files *)
  let all_cmd_line_files = expand_directories all_cmd_line_files in
  let all_cmd_line_files =
    match all_cmd_line_files with
    | [] -> all_files_in_include_paths ()
    | _ -> all_cmd_line_files
  in
  let all_cmd_line_files =
      all_cmd_line_files |> List.map (fun fn ->
        if Some? (FStarC.Parser.ParseIt.read_vfs_entry fn) then
          // This allows the IDE to check files that are not saved yet.
          fn
        else match Find.find_file fn with
        | None ->
          raise_error0 Errors.Fatal_ModuleOrFileNotFound
            (Format.fmt1 "File %s could not be found" fn)
        | Some fn -> fn) in
  // The dependency graph; keys are lowercased module names, values = list of
  // lowercased module names this file depends on.
  let dep_graph : dependence_graph = deps_empty () in
  // Cached parsing results for each file
  let parse_results = SMap.create 40 in
  // A map from lowercase module names (e.g. [a.b.c]) to the corresponding
  // filenames (e.g. [/where/to/find/A.B.C.fst]). Consider this map
  // immutable from there on.
  let file_system_map = SMap.create 41 in
  let valid_namespaces = SMap.create 41 in
  build_map file_system_map valid_namespaces all_cmd_line_files;
  let inlining_ifaces =
    build_dep_graph_for_files all_cmd_line_files all_cmd_line_files file_system_map dep_graph parse_results get_parsing_data_from_cache
  in

  debug_print (fun () -> print_graph stdout "stdout" dep_graph file_system_map all_cmd_line_files);

  (* At this point, dep_graph has all the (immediate) dependency graph of all the files. *)
  let cycle_detected (dep_graph:dependence_graph) cycle filename =
      let cycle = List.rev cycle in
      F.print1 "The cycle contains a subset of the modules in:\n  %s \n" (String.concat "\n  `uses` " cycle);

      (* Write the graph to a file for the user to see. *)
      let fn = "dep.graph" in
      with_file_outchannel fn (fun outc -> print_graph outc fn dep_graph file_system_map all_cmd_line_files);

      Format.print_string "\n";
      raise_error0 Errors.Fatal_CyclicDependence [
        text (Format.fmt1 "Recursive dependency on module %s." filename);
        text "A full dependency graph was written to dep.graph.";
      ]
  in
  (* full_cycle_detection finds cycles across interface
     boundaries that can otherwise be exploited to
     build cross-module recursive loops, as in issue #1391
  *)
  let full_cycle_detection all_command_line_files file_system_map =
    let dep_graph = dep_graph_copy dep_graph in

    (*
     * The cycle detection code considers all_command_line_files
     *   as roots to perform full cycle detection. As a result,
     *   all command line files, and their transitive dependences
     *   are considered. However, this misses the cycles through .fst
     *   as in the issue #1391, IF only .fsti is given on the command
     *   line. This is even more a problem in invocations like:
     *   fstar A.fsti --dep full, which dumps the .depend, while not
     *   noticing the cycle.
     *
     * A fix for this issue is to record in mo_files the implementations
     *   of command line interfaces whose implementations are not on the
     *   command line, and consider them also for cycle detection.
     *
     * Right now this is done even in the case of fstar A.fsti
     *   we can consider using mo_files only in the case of
     *   --dep invocations.
     *)
    let mo_files : ref (list string)  = mk_ref [] in


    let rec aux (cycle:list file_name) (filename: string) : ML unit =
        let node =
            match deps_try_find dep_graph filename with
            | Some node -> node
            | None ->
              failwith (Format.fmt1 "Impossible: Failed to find dependencies of %s" filename)
        in
        let direct_deps = node.edges |> List.collect (fun x ->
            match x with
            | UseInterface f
            | PreferInterface f ->
              begin
              match implementation_of_internal file_system_map f with
              | None -> [x]
              | Some fn when fn=filename ->
                //don't add trivial self-loops
                [x]
              | _  ->
                if peek_past_interfaces()
                then 
                    //if a module A uses B
                    //then detect cycles through both B.fsti
                    //and B.fst
                  [x; UseImplementation f]
                else [x]
              end
            | _ -> [x]) in
        match node.color with
        | Gray ->
          cycle_detected dep_graph cycle filename
        | Black ->
            (* If the element has been visited already, then the map contains all its
             * dependencies. Otherwise, the map only contains its direct dependencies. *)
            ()
        | White ->
            (* Unvisited. Compute. *)
            deps_add_dep dep_graph filename ({node with edges=direct_deps; color=Gray});
            List.iter (fun k -> aux (k :: cycle) k)
                      (dependences_of file_system_map
                                      dep_graph
                                      all_command_line_files
                                      filename);
            (* Mutate the graph (to mark the node as visited) *)
            deps_add_dep dep_graph filename ({node with edges=direct_deps; color=Black});

            (*
             * If the file is an interface, and its implementation exists, and the implementation
             *   is not on the command line, add it to mo_files
             *)
            if is_interface filename
            && peek_past_interfaces()
            then Option.iter
                  (fun impl -> if not (List.contains impl all_command_line_files)
                               then mo_files := impl::!mo_files
                               else ())
                  (implementation_of_internal file_system_map (lowercase_module_name filename))
            else ()
      in
      List.iter (aux []) all_command_line_files;
      (* Detect cycles via mo_files *)
      List.iter (aux []) !mo_files
  in
  full_cycle_detection all_cmd_line_files file_system_map;

  //only verify those files on the command line
  all_cmd_line_files |>
  List.iter (fun f ->
    let m = lowercase_module_name f in
    Options.add_verify_module m);

  let all_files, _ =
    profile
      (fun () ->
         topological_dependences_of
           file_system_map
           dep_graph
           inlining_ifaces
           all_cmd_line_files
           (Options.codegen()<>None))
      "FStarC.Parser.Dep.topological_dependences_of"
  in
  if !dbg
  then Format.print1 "Interfaces needing inlining: %s\n" (String.concat ", " inlining_ifaces);
  all_files,
  mk_deps dep_graph file_system_map valid_namespaces all_cmd_line_files (RBSet.from_list all_files) inlining_ifaces parse_results

(* In public interface *)
(* Every module the graph knows about, lowercased, in dependency order: a
   module comes after everything its implementation and its interface depend
   on.  This is the same walk [print_full] uses to order the .ml files it
   hands to the OCaml compiler, so it is the order the build links in.

   Whole-program extraction needs it to lay its output out (see
   [FStarC.Custard.Split]).  Ordering by the *file* graph is not enough there,
   because a module with an interface is reached through the interface alone
   and its implementation's dependencies never enter the order --
   [FStarC.Errors] would sort before [FStarC.Options] even though
   [FStarC.Errors.fst] uses it.

   [normalize] lets the caller collapse several source modules onto one node,
   which whole-program extraction needs because it emits several F* modules
   into one target module.  Collapsing can of course introduce a cycle where
   the source had none; the walk then breaks it at whichever end it reached
   first, as it must. *)
let topological_order (deps:deps) (normalize : module_name -> ML module_name)
  : ML (list module_name) =
  let norm (m:module_name) : ML module_name = normalize m in
  (* One node per normalized name, carrying the union of the edges of every
     file that maps to it -- implementation and interface alike. *)
  let edges : SMap.t (list module_name) = SMap.create 41 in
  let add (m:module_name) (ds:list module_name) : ML unit =
    let prev = Option.dflt [] (SMap.try_find edges m) in
    SMap.add edges m (ds @ prev) in
  let _ =
    deps_keys deps.dep_graph |> List.iter (fun f ->
      match maybe_module_name_of_file f with
      | None -> ()
      | Some m ->
        let ds =
          match deps_try_find deps.dep_graph f with
          | None -> []
          | Some ({edges=es}) -> es |> List.map (fun d -> norm (module_name_of_dep d)) in
        add (norm m) ds) in
  let order : ref (list module_name) = mk_ref [] in
  let visited = SMap.create 41 in
  let rec visit (m:module_name) : ML unit =
    if Some? (SMap.try_find visited m) then () else begin
      SMap.add visited m true;
      Option.dflt [] (SMap.try_find edges m) |> List.iter visit;
      order := m :: !order
    end in
  (* Command-line roots first, so that whatever they reach ranks before
     anything reached only from elsewhere.  Ties have to be broken somehow --
     two modules with no dependency between them can go in either order -- and
     "what the program being built needs, first" is the tie-break that matches
     the build: [fstar.exe]'s own modules come before the library modules it
     merely loads. *)
  deps.cmd_line_files |> List.iter (fun f ->
    match maybe_module_name_of_file f with
    | None -> ()
    | Some m -> visit (norm m));
  SMap.keys edges |> List.iter visit;
  List.rev !order

let parsing_data_of_modul deps filename modul_opt =
  let modul =
    match modul_opt with
    | None -> 
      let ast, _ = Driver.parse_file filename in
      ast
    | Some m -> m
  in
  let pd = collect_module_or_decls filename (Inl modul) in
  let pd = { pd with elts = List.rev pd.elts } in
  let direct_deps, _, _ = deps_from_parsing_data pd deps.file_system_map filename in
  pd, files_of_dependences filename deps.file_system_map deps.cmd_line_files direct_deps

(* A file the dependency scan never reached is simply absent from the graph,
   and the graph then reports it as having no dependences at all -- which is
   indistinguishable from the truth about Prims, and wrong for everyone else.
   Custard asks about such files: a plugin named by [--custard_entry] is a leaf
   of the program, not a dependence of the file on the command line.  Parsing
   answers the question, exactly as it does for the command-line file under
   [--ext fly_deps]. *)
let from_graph (deps:deps) (f:file_name) : ML (list file_name) =
  match deps_try_find deps.dep_graph f with
  | Some _ -> dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f
  | None -> snd (parsing_data_of_modul deps f None)

let deps_of =
  let cache = SMap.create 40 in
  fun deps (f:file_name) ->
    match SMap.try_find cache f with
    | Some deps -> deps
    | None ->
      let res =
        if fly_deps_enabled()
          then (
            let on_cli f =
              let bf = Filepath.basename f in
              List.existsb (fun cli -> Filepath.basename cli = bf) deps.cmd_line_files
            in
            if on_cli f
            || (is_interface f && implementation_of_file f |> on_cli)
            then (
              snd (parsing_data_of_modul deps f None)
            )
            else (
              from_graph deps f
            )
          )
      else from_graph deps f
    in
    SMap.add cache f res;
    res

let deps_of_modul deps (m:module_name) : ML (list module_name) =
  let aux (fopt:option string) =
    fopt |> Option.map (fun f -> f |> deps_of deps |> List.map module_name_of_file)
         |> Option.dflt []
  in
  m |> String.lowercase
    |> SMap.try_find deps.file_system_map
    |> Option.map (fun (intf_opt, impl_opt) ->
                      remove_dups_fast (aux intf_opt @ aux impl_opt))
    |> Option.dflt []

(* In public interface *)
let parsing_data_of deps fn =
  match SMap.try_find deps.parse_results fn with
  | None -> 
    failwith (Format.fmt1 "Parsing data not found for %s" fn)
  | Some pd -> pd

let populate_parsing_data fn ast_modul deps =
  match SMap.try_find deps.parse_results fn with
  | None -> 
    let pd = collect_module_or_decls fn (Inl ast_modul) in
    SMap.add deps.parse_results fn pd
  | Some _ -> ()

let print_digest (dig:list (string & string)) : ML string = show dig
    // dig
    // |> List.map (fun (m, d) -> Format.fmt2 "%s:%s" m (BU.base64_encode d))
    // |> String.concat "\n"

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

    Deprecated: this will print the dependences among the source files
  *)
let print_make (outc : out_channel) deps : ML unit =
    let file_system_map = deps.file_system_map in
    let all_cmd_line_files = deps.cmd_line_files in
    let deps = deps.dep_graph in
    let keys = deps_keys deps in
    keys |> List.iter
        (fun f ->
          let dep_node = deps_try_find deps f |> Option.must in
          let files = List.map (file_of_dep file_system_map all_cmd_line_files) dep_node.edges in
          let files = List.map (fun s -> replace_chars s ' ' "\\ ") files in
          //this one prints:
          //   a.fst: b.fst c.fsti a.fsti
          F.print2 "%s: %s\n\n" f (String.concat " " files))

(* In public interface *)
let print_raw (outc : out_channel) (deps:deps) =
    let (Deps deps) = deps.dep_graph in
      SMap.fold deps (fun k dep_node out ->
        Format.fmt2 "%s -> [\n\t%s\n] " k (List.map dep_to_string dep_node.edges |> String.concat ";\n\t") :: out) []
      |> String.concat ";;\n"
      |> (fun s -> BU.fprint outc "%s\n" [s])

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

     -- The dependences are among the .checked files

     -- We also print dependences for producing .ml files from .checked files
        This takes care of renaming A.B.C.fst to A_B_C.ml
  *)
let print_full (outc : out_channel) (deps:deps) : ML unit =
    let pre_tag = Options.Ext.get "dep_pretag" in
    //let (Mk (deps, file_system_map, all_cmd_line_files, all_files)) = deps in
    let sort_output_files (orig_output_file_map:SMap.t string) =
        let order : ref (list string) = mk_ref [] in
        let remaining_output_files = SMap.copy orig_output_file_map in
        let visited_other_modules = SMap.create 41 in
        let should_visit lc_module_name =
            Some? (SMap.try_find remaining_output_files lc_module_name)
            || None? (SMap.try_find visited_other_modules lc_module_name)
        in
        let mark_visiting lc_module_name =
            let ml_file_opt = SMap.try_find remaining_output_files lc_module_name in
            SMap.remove remaining_output_files lc_module_name;
            SMap.add visited_other_modules lc_module_name true;
            ml_file_opt
        in
        let emit_output_file_opt ml_file_opt =
            match ml_file_opt with
            | None -> ()
            | Some ml_file -> order := ml_file :: !order
        in
        let rec aux (ms: list string) : ML unit = match ms with
            | [] -> ()
            | lc_module_name::modules_to_extract ->
              let visit_file file_opt =
                match file_opt with
                | None -> ()
                | Some file_name ->
                  match deps_try_find deps.dep_graph file_name with
                  | None -> failwith (Format.fmt2 "Impossible: module %s: %s not found" lc_module_name file_name)
                  | Some ({edges=immediate_deps}) ->
                    let immediate_deps =
                        List.map (fun x -> String.lowercase (module_name_of_dep x)) immediate_deps
                    in
                    aux immediate_deps
              in
              if should_visit lc_module_name then begin
                 let ml_file_opt = mark_visiting lc_module_name in
                 //visit all its dependences
                 visit_file (implementation_of deps lc_module_name);
                 visit_file (interface_of deps lc_module_name);
                 //and then emit this one's ML file
                 emit_output_file_opt ml_file_opt
              end;
              aux modules_to_extract
        in
        let all_extracted_modules = SMap.keys orig_output_file_map in
        aux all_extracted_modules;
        List.rev !order
    in
    let sb = FStarC.StringBuffer.create 10000 in
    let pr str = ignore <| FStarC.StringBuffer.add str sb in
    let norm_path s = replace_chars (replace_chars s '\\' "/") ' ' "\\ " in
    let print_entry (target : string) (all_deps : list string) : ML unit =
        (* Print a target with dependencies. *)
        pr target; pr ":";
        all_deps |> List.iter (fun f -> pr " \\\n\t" ; pr (norm_path f));
        pr "\n\n"
    in
    let print_all tag files =
        (* Print a variable defined as a list of files *)
        pr (pre_tag^tag);
        pr "=";
        files |> List.iter (fun f -> pr " \\\n\t"; pr (norm_path f));
        pr "\n\n"
    in
    let keys = deps_keys deps.dep_graph in
    let no_fstar_stubs_file (s:string) : ML string =
      (* If the original filename begins with FStar.Stubs, then remove that,
      consistent with what extraction will actually do.

      This is VERY IMPORTANT for krml extraction, since we will generate
      the krml file even if we're not extracting these files (they are stubs!)
      per se. Make sure to run karamel tests (or a check-world) if you change this. *)
      let s1 = "FStar.Stubs." in
      let s2 = "FStar." in
      let l1 = String.length s1 in
      if String.length s >= l1 then
        let pfx = String.substring s 0 l1 in
        if pfx = s1 then
          s2 ^ String.substring s l1 (String.length s - l1)
        else
          s
      else
        s
    in
    let output_file ext fst_file =
        let basename = Option.must (check_and_strip_suffix (Filepath.basename fst_file)) in
        let basename = no_fstar_stubs_file basename in
        let ml_base_name = replace_chars basename '.' "_" in
        Find.prepend_output_dir (ml_base_name ^ ext)
    in
    let output_fs_file   f = norm_path <| output_file ".fs" f in
    let output_ml_file   f = norm_path <| output_file ".ml" f in
    let output_krml_file f = norm_path <| output_file ".krml" f in
    let output_cmx_file  f = norm_path <| output_file ".cmx" f in
    let cache_file       f = norm_path <| cache_file_name f in
    let widened, dep_graph = phase1 deps.file_system_map deps.dep_graph deps.interfaces_with_inlining true in
    let all_checked_files =
        keys |>
        List.fold_left
        (fun all_checked_files file_name ->
          let process_one_key () =
            let dep_node = deps_try_find deps.dep_graph file_name |> Option.must in
            let iface_fn, iface_deps =
                if is_interface file_name
                then None, None
                else match interface_of deps (lowercase_module_name file_name) with
                     | None ->
                       None, None
                     | Some iface ->
                       Some iface,
                       Some ((Option.must (deps_try_find deps.dep_graph iface)).edges)
            in
            let iface_deps =
                Option.map (List.filter
                             (fun iface_dep ->
                                not (BU.for_some (dep_subsumed_by iface_dep) dep_node.edges)))
                           iface_deps
            in
            let files =
              List.map
                (file_of_dep_aux true deps.file_system_map deps.cmd_line_files)
                dep_node.edges
            in
            let files =
                match iface_deps with
                | None -> files
                | Some iface_deps ->
                  let iface_files =
                      List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) iface_deps
                  in
                  remove_dups_fast (files @ iface_files)
            in

            (*
             * AR: depend on A.fsti.checked, rather than A.fsti
             *     see #1919
             *)
            let files =
              if iface_fn |> Some? then
                let iface_fn = iface_fn |> Option.must in
                files |> List.filter (fun f -> f <> iface_fn)
                      |> (fun files -> (cache_file_name iface_fn)::files)
              else files in

            let cache_file_name = cache_file file_name in

            let all_checked_files =
                if not (Options.should_be_already_cached (module_name_of_file file_name))
                then //this one prints:
                     //   a.fst.checked: b.fst.checked c.fsti.checked a.fsti
                     (print_entry cache_file_name (file_name :: files);
                      cache_file_name::all_checked_files)
                else all_checked_files
            in

            //And, if this is not an interface, we also print out the dependences among the .ml files
            // excluding files in ulib, since these are packaged in fstar_lib.cmxa
          let all_fst_files_dep, widened =
              if Options.cmi()
              then profile
                   (fun () ->
                     topological_dependences_of'
                     deps.file_system_map
                     (dep_graph_copy dep_graph)
                     deps.interfaces_with_inlining
                     [file_name]
                     widened)
                    "FStarC.Parser.Dep.topological_dependences_of_2"
              else
                   let maybe_widen_deps (f_deps:dependences) =
                      List.map
                        (fun dep ->
                          file_of_dep_aux false deps.file_system_map deps.cmd_line_files dep)
                        f_deps
                   in
                   let fst_files = maybe_widen_deps dep_node.edges in
                   let fst_files_from_iface =
                        match iface_deps with
                        | None -> []
                        | Some iface_deps -> maybe_widen_deps iface_deps
                   in
                   remove_dups_fast (fst_files @ fst_files_from_iface),
                   false
          in
          let all_checked_fst_dep_files = all_fst_files_dep |> List.map cache_file in
          let _ =
            if is_implementation file_name
            then begin
              if Options.cmi()
              && widened
              then begin
                     let mname = lowercase_module_name file_name in

                     print_entry
                        (output_ml_file file_name)
                        (cache_file_name :: all_checked_fst_dep_files);

                     if Options.should_extract mname Options.FSharp
                     then print_entry
                            (output_fs_file file_name)
                            (cache_file_name :: all_checked_fst_dep_files);

                     print_entry
                        (output_krml_file file_name)
                        (cache_file_name :: all_checked_fst_dep_files)
              end
              else begin
                     let mname = lowercase_module_name file_name in

                     print_entry
                        (output_ml_file file_name)
                        [cache_file_name];

                     if Options.should_extract mname Options.FSharp
                     then print_entry
                            (output_fs_file file_name)
                            [cache_file_name];

                     print_entry
                        (output_krml_file file_name)
                        [cache_file_name]
              end;
              let cmx_files =
                  let extracted_fst_files =
                      all_fst_files_dep |>
                      List.filter
                        (fun df ->
                           let mn_df = lowercase_module_name df in
                           let mn_fn = lowercase_module_name file_name in
                           mn_df <> mn_fn //avoid circular deps on f's own cmx
                           && Options.should_extract mn_df Options.OCaml)
                  in
                  extracted_fst_files |> List.map output_cmx_file
              in
              if Options.should_extract (lowercase_module_name file_name) Options.OCaml
              then
                print_entry
                    (output_cmx_file file_name)
                    (output_ml_file file_name :: cmx_files)

            end
            else if not(has_implementation deps.file_system_map (lowercase_module_name file_name))
                 && is_interface file_name
            then begin
                // .krml files can be produced using just an interface, unlike .ml files
                if Options.cmi()
                && (widened || true)
                then
                    print_entry
                        (output_krml_file file_name)
                        (cache_file_name :: all_checked_fst_dep_files)
                else
                   print_entry
                    (output_krml_file file_name)
                    [cache_file_name]
            end
          in
          all_checked_files
        in
        profile process_one_key "FStarC.Parser.Dep.process_one_key")
        []
    in
    let all_fst_files =
      keys |> List.filter is_implementation
           |> Util.sort_with String.compare
    in
    let all_fsti_files =
      keys |> List.filter is_interface
           |> Util.sort_with String.compare
    in
    let all_ml_files =
        let ml_file_map = SMap.create 41 in
        all_fst_files
        |> List.iter (fun fst_file ->
                       let mname = lowercase_module_name fst_file in
                       if Options.should_extract mname Options.OCaml
                       then SMap.add ml_file_map mname (output_ml_file fst_file));
        sort_output_files ml_file_map
    in
    let all_fs_files =
        let fs_file_map = SMap.create 41 in
        all_fst_files
        |> List.iter (fun fst_file ->
                       let mname = lowercase_module_name fst_file in
                       if Options.should_extract mname Options.FSharp
                       then SMap.add fs_file_map mname (output_fs_file fst_file));
        sort_output_files fs_file_map
    in
    let all_krml_files =
        let krml_file_map = SMap.create 41 in
        keys
        |> List.iter (fun fst_file ->
                       let mname = lowercase_module_name fst_file in
                       if Options.should_extract mname Options.Krml
                       then SMap.add krml_file_map mname (output_krml_file fst_file));
        sort_output_files krml_file_map
    in
    all_fsti_files
    |> List.iter
      (fun fsti ->
         let mn = lowercase_module_name fsti in
         let range_of_file fsti =
           let r = Range.set_file_of_range Range.dummyRange fsti in
           Range.set_use_range r (Range.def_range r)
         in
         if not (has_implementation deps.file_system_map mn) then
           log_issue (range_of_file fsti) Warning_WarnOnUse
             (Format.fmt1 "Interface %s is admitted without an implementation" (module_name_of_file fsti)));
    print_all "ALL_FST_FILES" all_fst_files;
    print_all "ALL_FSTI_FILES" all_fsti_files;
    print_all "ALL_CHECKED_FILES" all_checked_files;
    print_all "ALL_FS_FILES" all_fs_files;
    print_all "ALL_ML_FILES" all_ml_files;
    print_all "ALL_KRML_FILES" all_krml_files;

    FStarC.StringBuffer.output_channel outc sb

(** Print the dependencies in dune format.
    When --output_ext is set, controls what targets are emitted:
    - Extensions ending in "checked": build/check rules (.fst → .fst.checked)
    - Other extensions (ml, krml): extraction rules (.fst.checked → .ml)
    When --output_ext is not set: mixed rules (backward compat).
  *)
let print_dune (outc : out_channel) (deps:deps) : ML unit =
    let sb = FStarC.StringBuffer.create 10000 in
    let pr str = ignore <| FStarC.StringBuffer.add str sb in
    
    let output_ext = Options.output_ext () in
    
    (* Is this an extraction phase? (output-ext is ml, krml, etc.) *)
    let is_extract_phase =
        match output_ext with
        | Some ext -> not (BU.ends_with ext "checked")
        | None -> false
    in
    
    (* Replace the F* source suffix (.fst/.fsti) with a new extension *)
    let replace_suffix (f:string) (new_ext:string) : ML string =
        let base = Filepath.basename f in
        match check_and_strip_suffix base with
        | Some stem -> stem ^ "." ^ new_ext
        | None -> base ^ "." ^ new_ext
    in
    
    (* Collect flags to forward into generated rules.
       We take all argv flags except --dep/--already_cached/--output_ext and
       positional file/directory arguments. *)
    let forwarded_flags =
        let args = BU.get_cmd_args () in
        (* Drop the executable name *)
        let args = match args with | _::tl -> tl | [] -> [] in
        let rec collect acc = function
          | [] -> List.rev acc
          (* Skip --dep and its argument *)
          | "--dep"::_::rest -> collect acc rest
          (* Skip --already_cached and its argument *)
          | "--already_cached"::_::rest -> collect acc rest
          (* Skip --output_ext and its argument (both dash and underscore forms) *)
          | "--output_ext"::_::rest -> collect acc rest
          | "--output-ext"::_::rest -> collect acc rest
          (* Keep flags and their arguments *)
          | flag::rest when BU.starts_with flag "-" ->
            begin match rest with
            | arg::rest' when not (BU.starts_with arg "-") && arg <> "" ->
              collect ((" " ^ arg)::(" " ^ flag)::acc) rest'
            | _ ->
              collect ((" " ^ flag)::acc) rest
            end
          (* Skip positional arguments (file/directory paths) *)
          | _::rest -> collect acc rest
        in
        String.concat "" (collect [] args)
    in
    
    let keys = deps_keys deps.dep_graph in
    (* For dune: put checked files in current directory, not next to source *)
    let local_cache_file (f:string) : ML string =
        let base = Filepath.basename f in
        base ^ ".checked"
    in
    
    (* Format a dep: all files become local basename *)
    let format_dep (f:string) : ML string =
        Filepath.basename f
    in
    
    (* Compute the extraction target for a source file, if codegen is set.
       Used only in default mixed mode (no --output_ext). *)
    let extraction_target (source : string) : ML (option string) =
        match Options.codegen () with
        | Some Options.OCaml ->
            let basename = Option.must (check_and_strip_suffix (Filepath.basename source)) in
            let ml_base_name = replace_chars basename '.' "_" in
            if is_implementation source then Some (ml_base_name ^ ".ml")
            else None
        | Some Options.Krml ->
            let basename = Option.must (check_and_strip_suffix (Filepath.basename source)) in
            let ml_base_name = replace_chars basename '.' "_" in
            if is_implementation source then Some (ml_base_name ^ ".krml")
            else None
        | _ -> None
    in
    
    (* Print a rule for default mixed mode: checking and optionally extracting *)
    let print_mixed_rule (target : string) (source : string) (all_deps : list string) : ML unit =
        let extra_target = extraction_target source in
        pr "(rule\n";
        pr " (targets "; pr target;
        (match extra_target with | Some t -> pr " "; pr t | None -> ());
        pr ")\n";
        pr " (deps"; 
        all_deps |> List.iter (fun f -> pr " "; pr (format_dep f));
        pr ")\n";
        pr " (action (run %{env:FSTAR_EXE=fstar.exe}";
        pr forwarded_flags;
        pr " --include . --already_cached \"*,\" -c ";
        pr (Filepath.basename source); pr ")))\n\n"
    in
    
    (* Print a rule for the build phase: source → checked *)
    let print_build_rule (source : string) (all_deps : list string) : ML unit =
        let ext = Option.must output_ext in
        let target = replace_suffix source ext in
        pr "(rule\n";
        pr " (targets "; pr target; pr ")\n";
        pr " (deps";
        all_deps |> List.iter (fun f -> pr " "; pr (format_dep f));
        pr ")\n";
        pr " (action (run %{env:FSTAR_EXE=fstar.exe}";
        pr forwarded_flags;
        pr " --include . --already_cached \"*,\" -c ";
        pr (Filepath.basename source); pr ")))\n\n"
    in
    
    (* Print a rule for the extraction phase: checked → ml/krml *)
    let print_extract_rule (source : string) (all_deps : list string) : ML unit =
        let ext = Option.must output_ext in
        let target = replace_suffix source ext in
        (* Convert all source deps to their checked versions *)
        let checked_deps =
            (source :: all_deps) |> List.map (fun f ->
                let base = Filepath.basename f in
                if BU.ends_with base ".checked"
                then base
                else local_cache_file f
            )
        in
        (* Deps: source file + checked source + checked transitive deps *)
        let all_dep_strs = format_dep source :: checked_deps in
        pr "(rule\n";
        pr " (targets "; pr target; pr ")\n";
        pr " (deps";
        (remove_dups_fast all_dep_strs) |> List.iter (fun f -> pr " "; pr f);
        pr ")\n";
        pr " (action (run %{env:FSTAR_EXE=fstar.exe}";
        pr forwarded_flags;
        pr " --include . --already_cached \"*,\" -c ";
        pr (Filepath.basename source); pr ")))\n\n"
    in
    
    let widened, dep_graph = phase1 deps.file_system_map deps.dep_graph deps.interfaces_with_inlining true in
    
    (* Collect all target files *)
    let all_target_files =
        keys |>
        List.fold_left
        (fun all_target_files file_name ->
          let process_one_key () =
            (* In extract phase, skip non-implementation files *)
            if is_extract_phase && not (is_implementation file_name) then
              all_target_files
            else begin
            let dep_node = deps_try_find deps.dep_graph file_name |> Option.must in
            let iface_fn, iface_deps =
                if is_interface file_name
                then None, None
                else match interface_of deps (lowercase_module_name file_name) with
                     | None ->
                       None, None
                     | Some iface ->
                       Some iface,
                       Some ((Option.must (deps_try_find deps.dep_graph iface)).edges)
            in
            let iface_deps =
                Option.map (List.filter
                             (fun iface_dep ->
                                not (BU.for_some (dep_subsumed_by iface_dep) dep_node.edges)))
                           iface_deps
            in
            let files =
              List.map
                (file_of_dep_aux true deps.file_system_map deps.cmd_line_files)
                dep_node.edges
            in
            let files =
                match iface_deps with
                | None -> files
                | Some iface_deps ->
                  let iface_files =
                      List.map (file_of_dep_aux true deps.file_system_map deps.cmd_line_files) iface_deps
                  in
                  remove_dups_fast (files @ iface_files)
            in
            let files =
              if iface_fn |> Some? then
                let iface_fn = iface_fn |> Option.must in
                files |> List.filter (fun f -> f <> iface_fn)
                      |> (fun files -> (local_cache_file iface_fn)::files)
              else files in

            (* Filter out deps on already-cached modules; fstar resolves them
               at runtime via --already_cached, so dune need not track them. *)
            let files =
              files |> List.filter (fun f ->
                let base = Filepath.basename f in
                (* Strip .checked suffix to recover source name *)
                let src =
                  if BU.ends_with base ".checked" then String.substring base 0 (String.length base - 8)
                  else base
                in
                match check_and_strip_suffix src with
                | Some mname -> not (Options.should_be_already_cached mname)
                | None -> true (* keep non-module deps *)
              )
            in

            let target_file =
                match output_ext with
                | Some ext -> replace_suffix file_name ext
                | None -> local_cache_file file_name
            in

            let all_target_files =
                if not (Options.should_be_already_cached (module_name_of_file file_name))
                then begin
                  if is_extract_phase then
                    print_extract_rule file_name files
                  else if Some? output_ext then
                    print_build_rule file_name (file_name :: files)
                  else
                    print_mixed_rule (local_cache_file file_name) file_name (file_name :: files);
                  target_file::all_target_files
                end
                else all_target_files
            in

            all_target_files
            end
          in
          profile process_one_key "FStarC.Parser.Dep.print_dune.process_one_key")
          []
    in
    
    pr "; File lists (for reference)\n";
    pr "; ALL_TARGET_FILES:";
    all_target_files |> List.iter (fun f -> pr " "; pr f);
    pr "\n";

    FStarC.StringBuffer.output_channel outc sb

let do_print (outc : out_channel) (fn : string) deps : ML unit =
  let print_header (comment : string) (kind : string) =
    let ver = BU.trim_string !Options._version in
    BU.fprint outc (comment ^ " This %s was generated by F* %s\n") [kind; ver];
    BU.fprint outc (comment ^ " Executable: %s\n") [show BU.exec_name];
    BU.fprint outc (comment ^ " Hash: %s\n") [BU.trim_string !Options._commit];
    BU.fprint outc (comment ^ " Running in directory %s\n") [show (Filepath.normalize_file_path (BU.getcwd ()))];
    BU.fprint outc (comment ^ " Command line arguments: \"%s\"\n") [show (BU.get_cmd_args ())];
    BU.fprint outc "\n" []
  in
  let pref      () = print_header "#" ".depend" in
  let dune_pref () = print_header ";" "dune file" in
  match Options.dep() with
  | Some "make" ->
      pref ();
      print_make outc deps
  | Some "full" ->
      pref ();
      profile (fun () -> print_full outc deps) "FStarC.Parser.Deps.print_full_deps"
  | Some "dune" ->
      dune_pref ();
      profile (fun () -> print_dune outc deps) "FStarC.Parser.Deps.print_dune_deps"
  | Some "graph" ->
      print_graph outc fn deps.dep_graph deps.file_system_map deps.cmd_line_files
  | Some "raw" ->
      print_raw outc deps
  | Some _ ->
      raise_error0 Errors.Fatal_UnknownToolForDep "unknown tool for --dep\n"
  | None ->
      assert false

(* Just prints to stdout *)
let do_print_stdout deps =
  do_print BU.stdout "<stdout>" deps

(* Opens the file, prints to it, and closes it. If anything failed, the file
is deleted. *)
let do_print_file deps fn =
  with_file_outchannel fn (fun outc -> do_print outc fn deps)

(* In public interface *)
let print deps =
  match Options.output_deps_to () with
  | Some s -> do_print_file deps s
  (* Special case for --dep graph, by default we write to dep.graph instead of stdout. *)
  | None when Options.dep () = Some "graph" -> do_print_file deps "dep.graph"
  | None -> do_print_stdout deps

(* In public interface *)
let module_has_interface deps module_name =
    has_interface deps.file_system_map (String.lowercase (Ident.string_of_lid module_name))

(* In public interface *)
let deps_has_implementation deps module_name =
    let m = String.lowercase (Ident.string_of_lid module_name) in
    RBSet.elems !deps.all_files |> BU.for_some (fun f ->
        is_implementation f
        && String.lowercase (module_name_of_file f) = m)

let all_files deps = RBSet.elems !deps.all_files

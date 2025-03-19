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
module FStarC.Parser.Dep

open FStarC
open FStarC.Effect   //for ref, failwith etc
open FStarC.List
open FStarC.Parser.AST
open FStarC.Const
open FStarC.Errors
open FStarC.Class.Show

module Const = FStarC.Parser.Const
module BU = FStarC.Util

let dbg              = Debug.get_toggle "Dep"
let dbg_CheckedFiles = Debug.get_toggle "CheckedFiles"

let profile f c = Profiling.profile f None c

(* Meant to write to a file as an out_channel. If an exception is raised,
the file is deleted. *)
let with_file_outchannel (fn : string) (k : out_channel -> 'a) : 'a =
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
  BU.print_string "Printing the file system map {\n";
  let str_opt_to_string sopt =
    match sopt with
    | None -> "<None>"
    | Some s -> s in
  SMap.iter m (fun k v -> BU.print2 "%s:%s\n" k (intf_and_impl_to_string v));
  BU.print_string "}\n"

type color = | White | Gray | Black

let check_and_strip_suffix (f: string): option string =
  let suffixes = [ ".fsti"; ".fst" ] in
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
let maybe_module_name_of_file f = check_and_strip_suffix (Filepath.basename f)
let module_name_of_file f =
    match maybe_module_name_of_file f with
    | Some longname ->
      longname
    | None ->
      raise_error0 Errors.Fatal_NotValidFStarFile (
        [ text <| Util.format1 "Not a valid FStar file: '%s'" f; ] @
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

(*
 * AR: Parsing data for a file (also cached in the checked files)
 *     It is a summary of opens, includes, A.<id>, etc. in a module
 *     Earlier we used to store the dependences in the checked file,
 *       however that is an image of the file system, and so, when the checked
 *       files were used in a slightly different file system, there were strange errors
 *       see e.g. #1657 for a couple of cases
 *     Now we store the following summary and construct the dependences from the current
 *       file system
 *)
type parsing_data_elt =
  | P_begin_module of lident  //begin_module
  | P_open of bool & lident  //record_open
  | P_implicit_open_module_or_namespace of (open_kind & lid)  //record_open_module_or_namespace
  | P_dep of bool & lident  //add_dep_on_module, bool=true iff it's a friend dependency
  | P_alias of ident & lident  //record_module_alias
  | P_lid of lident  //record_lid
  | P_inline_for_extraction

type parsing_data = {
    elts : list parsing_data_elt;
    no_prelude : bool;
}

let str_of_parsing_data_elt elt =
  let str_of_open_kind = function
    | Open_module -> "P_open_module"
    | Open_namespace -> "P_open_namespace"
  in
  match elt with
  | P_begin_module lid -> "P_begin_module (" ^ (string_of_lid lid) ^ ")"
  | P_open (b, lid) -> "P_open (" ^ (string_of_bool b) ^ ", " ^ (string_of_lid lid) ^ ")"
  | P_implicit_open_module_or_namespace (k, lid) -> "P_implicit_open_module_or_namespace (" ^ (str_of_open_kind k) ^ ", " ^ (string_of_lid lid) ^ ")"
  | P_dep (b, lid) -> "P_dep (" ^ (string_of_lid lid) ^ ", " ^ (string_of_bool b) ^ ")"
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

let friends (p:parsing_data) : list lident =
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
    cmd_line_files:list file_name;              //all command-line files
    all_files:list file_name;                   //all files
    interfaces_with_inlining:list module_name;  //interfaces that use `inline_for_extraction` require inlining
    parse_results:SMap.t parsing_data             //map from filenames to parsing_data
                                                //callers (Universal.fs) use this to get the parsing data for caching purposes
}
let deps_try_find (Deps m) k = SMap.try_find m k
let deps_add_dep (Deps m) k v =
  SMap.add m k v
let deps_keys (Deps m) = SMap.keys m
let deps_empty () = Deps (SMap.create 41)
let mk_deps dg fs c a i pr = {
    dep_graph=dg;
    file_system_map=fs;
    cmd_line_files=c;
    all_files=a;
    interfaces_with_inlining=i;
    parse_results=pr;
}
(* In public interface *)
let empty_deps = mk_deps (deps_empty ()) (SMap.create 0) [] [] [] (SMap.create 0)
let module_name_of_dep = function
    | UseInterface m
    | PreferInterface m
    | UseImplementation m
    | FriendImplementation m -> m

let resolve_module_name (file_system_map:files_for_module_name) (key:module_name)
    : option module_name
    = match SMap.try_find file_system_map key with
      | Some (Some fn, _)
      | Some (_, Some fn) -> Some (lowercase_module_name fn)
      | _ -> None

let interface_of_internal (file_system_map:files_for_module_name) (key:module_name)
    : option file_name =
    match SMap.try_find file_system_map key with
    | Some (Some iface, _) -> Some iface
    | _ -> None

let implementation_of_internal (file_system_map:files_for_module_name) (key:module_name)
    : option file_name =
    match SMap.try_find file_system_map key with
    | Some (_, Some impl) -> Some impl
    | _ -> None

let interface_of deps key = interface_of_internal deps.file_system_map key
let implementation_of deps key = implementation_of_internal deps.file_system_map key

let has_interface (file_system_map:files_for_module_name) (key:module_name)
    : bool =
    Option.isSome (interface_of_internal file_system_map key)

let has_implementation (file_system_map:files_for_module_name) (key:module_name)
    : bool =
    Option.isSome (implementation_of_internal file_system_map key)


(*
 * Public interface
 *)
let cache_file_name =
    let checked_file_and_exists_flag fn =
      let cache_fn =
        let lax = Options.lax () in
        if lax then fn ^".checked.lax"
        else fn ^".checked"
      in
      let mname = fn |> module_name_of_file in
      match Find.find_file (cache_fn |> Filepath.basename) with
      | Some path ->
        let expected_cache_file = Find.prepend_cache_dir cache_fn in
        if Option.isSome (Options.dep()) //if we're in the dependence analysis
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
          BU.print1 "find_file(%s) returned None\n" (cache_fn |> Filepath.basename);
        if mname |> Options.should_be_already_cached then
          raise_error0 FStarC.Errors.Error_AlreadyCachedAssertionFailure [
             text (BU.format1 "Expected %s to be already checked but could not find it." mname)
           ];
        Find.prepend_cache_dir cache_fn
    in
    let memo = SMap.create 100 in
    let memo f x =
      match SMap.try_find memo x with
      | Some res -> res
      | None ->
        let res = f x in
        SMap.add memo x res;
        res
    in
    memo checked_file_and_exists_flag

let parsing_data_of deps fn = SMap.try_find deps.parse_results fn |> must

let file_of_dep_aux
                (use_checked_file:bool)
                (file_system_map:files_for_module_name)
                (all_cmd_line_files:list file_name)
                (d:dependence)
    : file_name =
    let cmd_line_has_impl key =
        all_cmd_line_files
        |> BU.for_some (fun fn ->
           is_implementation fn &&
           key = lowercase_module_name fn)
    in

    let maybe_use_cache_of f = if use_checked_file then cache_file_name f else f in

    match d with
    | UseInterface key ->
      //This key always resolves to an interface source file
      (match interface_of_internal file_system_map key with
       | None ->
         assert false; //should be unreachable; see the only use of UseInterface in discover_one
         raise_error0 Errors.Fatal_MissingInterface (BU.format1 "Expected an interface for module %s, but couldn't find one" key)
       | Some f ->
         f)

    | PreferInterface key //key for module 'a'
        when has_interface file_system_map key ->  //so long as 'a.fsti' exists
      if cmd_line_has_impl key //unless the cmd line contains 'a.fst'
      && Option.isNone (Options.dep()) //and we're not just doing a dependency scan using `--dep _`
      then if Options.expose_interfaces()
           then maybe_use_cache_of (Option.get (implementation_of_internal file_system_map key))
           else raise_error0 Errors.Fatal_MissingExposeInterfacesOption [
                    text <| BU.format3 "You may have a cyclic dependence on module %s: use --dep full to confirm. \
                                Alternatively, invoking fstar with %s on the command line breaks \
                                the abstraction imposed by its interface %s."
                                key
                                (Option.get (implementation_of_internal file_system_map key))
                                (Option.get (interface_of_internal file_system_map key));
                    text "If you really want this behavior add the option '--expose_interfaces'.";
                  ]
      else maybe_use_cache_of (Option.get (interface_of_internal file_system_map key))   //we prefer to use 'a.fsti'

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
            (BU.format1 "Expected an implementation of module %s, but couldn't find one" key)
        | Some f -> maybe_use_cache_of f

let file_of_dep = file_of_dep_aux false

let dependences_of (file_system_map:files_for_module_name)
                   (deps:dependence_graph)
                   (all_cmd_line_files:list file_name)
                   (fn:file_name)
    : list file_name =
    match deps_try_find deps fn with
    | None -> empty_dependences
    | Some ({edges=deps}) ->
      List.map (file_of_dep file_system_map all_cmd_line_files) deps
      |> List.filter (fun k -> k <> fn) (* skip current module, cf #451 *)

let print_graph (outc : out_channel) (fn : string) (graph:dependence_graph)
  (file_system_map:files_for_module_name)
  (cmd_lined_files:list file_name)
 : unit
 =
  if not (Options.silent ()) then begin
    Util.print1 "A DOT-format graph has been dumped in the current directory as `%s`\n" fn;
    Util.print1 "With GraphViz installed, try: fdp -Tpng -odep.png %s\n" fn;
    Util.print1 "Hint: cat %s | grep -v _ | grep -v prims\n" fn
  end;
  let sb = FStarC.StringBuffer.create 10000 in
  let pr str = ignore <| FStarC.StringBuffer.add str sb in
  pr "digraph {\n";
  List.unique (deps_keys graph) |> List.iter (fun k ->
    let deps = (must (deps_try_find graph k)).edges in
    List.iter (fun dep ->
      let l = Filepath.basename k in
      let r = Filepath.basename <| file_of_dep file_system_map cmd_lined_files dep in
      if not <| Options.should_be_already_cached (module_name_of_dep dep) then
        pr (Util.format2 "  \"%s\" -> \"%s\"\n" l r)
    ) deps
  );
  pr "}\n";
  fprint outc "%s" [FStarC.StringBuffer.contents sb]

let safe_readdir_for_include (d:string) : list string =
  try Filepath.readdir d
  with
  | _ -> []

(** Enumerate all F* files in include directories.
    Return a list of pairs of long names and full paths. *)
(* In public interface *)
let build_inclusion_candidates_list (): list (string & string) =
  let include_directories = Find.full_include_path () in
  let include_directories = List.map Filepath.normalize_file_path include_directories in
  (* Note that [BatList.unique] keeps the last occurrence, that way one can
   * always override the precedence order. *)
  let include_directories = List.unique include_directories in
  let cwd = Filepath.normalize_file_path (getcwd ()) in
  include_directories |> List.concatMap (fun d ->
    let files = safe_readdir_for_include d in
    files |> List.filter_map (fun f ->
      let f = Filepath.basename f in
      check_and_strip_suffix f
      |> Util.map_option (fun longname ->
            let full_path = if d = cwd then f else Filepath.join_paths d f in
            (longname, full_path))
    )
  )

(** List the contents of all include directories, then build a map from long
    names (e.g. a.b) to pairs of filenames (/path/to/A.B.fst). Long names are
    all normalized to lowercase. The first component of the pair is the
    interface (if any). The second component of the pair is the implementation
    (if any). *)
let build_map (filenames: list string): files_for_module_name =
  let map = SMap.create 41 in
  let add_entry key full_path =
    match SMap.try_find map key with
    | Some (intf, impl) ->
        if is_interface full_path then
          SMap.add map key (Some full_path, impl)
        else
          SMap.add map key (intf, Some full_path)
    | None ->
        if is_interface full_path then
          SMap.add map key (Some full_path, None)
        else
          SMap.add map key (None, Some full_path)
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

let check_module_declaration_against_filename (lid: lident) (filename: string): unit =
  let k' = string_of_lid lid true in
  if must (check_and_strip_suffix (Filepath.basename filename)) <> k' then
    log_issue lid Errors.Error_ModuleFileNameMismatch [
        Errors.Msg.text (Util.format2 "The module declaration \"module %s\" \
          found in file %s does not match its filename." (string_of_lid lid true) filename);
        Errors.Msg.text "Dependencies will be incorrect and the module will not be verified.";
      ]

exception Exit

let dep_subsumed_by d d' =
      match d, d' with
      | PreferInterface l', FriendImplementation l -> l=l'
      | _ -> d = d'

(** For all items [i] in the map that start with [prefix], add an additional
    entry where [i] stripped from [prefix] points to the same value. Returns a
    boolean telling whether the map was modified.

    If the open is an implicit open (as indicated by the flag),
    and doing so shadows an existing entry, warn! *)
let enter_namespace
  (original_map: files_for_module_name)
  (working_map: files_for_module_name)
  (sprefix: string)
  (implicit_open:bool) : bool =
  let found = mk_ref false in
  let sprefix = sprefix ^ "." in
  let suffix_exists mopt =
    match mopt with
    | None -> false
    | Some (intf, impl) -> is_some intf || is_some impl in
  SMap.iter original_map (fun k _ ->
    if Util.starts_with k sprefix then
      let suffix =
        String.substring k (String.length sprefix) (String.length k - String.length sprefix)
      in

      begin
        let suffix_filename = SMap.try_find original_map suffix in
        if implicit_open &&
           suffix_exists suffix_filename
        then let str = suffix_filename |> must |> intf_and_impl_to_string in
             let open FStarC.Pprint in
             log_issue0 Errors.Warning_UnexpectedFile [
                flow (break_ 1) [
                  text "Implicitly opening namespace";
                  squotes (doc_of_string sprefix);
                  text "shadows module";
                  squotes (doc_of_string suffix);
                  text "in file";
                  dquotes (doc_of_string str) ^^ dot;
                ];
                text "Rename" ^/^ dquotes (doc_of_string str) ^/^ text "to avoid conflicts.";
             ]
      end;

      let filename = must (SMap.try_find original_map k) in
      SMap.add working_map suffix filename;
      found := true
  );
  !found

let prelude : list (open_kind & lid) = [
   (Open_namespace, Const.fstar_ns_lid);
   (Open_module,    Ident.lid_of_str "FStar.Prelude");
]

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
  (get_parsing_data_from_cache:string -> option parsing_data)
  : parsing_data &
    list dependence &  //direct dependence
    bool &  //has_inline_for_extraction
    list dependence  //additional roots
                      //that used to be part of parsing_data earlier
                      //removing it from the cache (#1657)
                      //this always returns a single element, remove the list?
=
  (*
   * Construct dependences from the parsing data
   * This is common function for when the parsing data is read from the checked files
   *   or constructed after AST traversal of the module
   *)
  let from_parsing_data (pd:parsing_data) (original_map:files_for_module_name) (filename:string)
    : list dependence &
      bool &
      list dependence
    =  let deps     : ref (list dependence) = mk_ref [] in
       let has_inline_for_extraction = mk_ref false in

       let mname = lowercase_module_name filename in
       let mo_roots =
         if is_interface filename
         && has_implementation original_map mname
         then [ UseImplementation mname ]
         else []
       in

       let auto_open =
         if pd.no_prelude
         then []
         else
           (prelude |> List.map (fun (k, l) -> P_open (false, l)))
           @
           (match namespace_of_module mname with
             | None -> []
             | Some ns -> [ P_implicit_open_module_or_namespace (Open_namespace, ns) ])
       in

       let working_map = SMap.copy original_map in

       let set_interface_inlining () =
         if is_interface filename
         then has_inline_for_extraction := true
       in

       let add_dep deps d =
         if not (List.existsML (dep_subsumed_by d) !deps) then
           deps := d :: !deps
       in

       let dep_edge module_name is_friend =
         if is_friend then FriendImplementation module_name
         else PreferInterface module_name
       in

       let add_dependence_edge original_or_working_map lid is_friend =
         let key = lowercase_join_longident lid true in
         match resolve_module_name original_or_working_map key with
         | Some module_name ->
           add_dep deps (dep_edge module_name is_friend);
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
               (Util.format1 "Module not found: %s" (string_of_lid lid true));
           false
         end
       in

       let record_open_namespace lid (implicit_open:bool) =
         let key = lowercase_join_longident lid true in
         let r = enter_namespace original_map working_map key implicit_open in
         if not r && not implicit_open then  //suppress the warning for implicit opens
           log_issue lid Errors.Warning_ModuleOrFileNotFoundWarning
             (Util.format1 "No modules in namespace %s and no file with that name either" (string_of_lid lid true))
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
           add_dep deps (dep_edge (lowercase_join_longident lid true) false);
           true
         | None ->
           log_issue lid Errors.Warning_ModuleOrFileNotFoundWarning
             (Util.format1 "module not found in search path: %s" alias);
           false
       in

       let add_dep_on_module (module_name : lid) (is_friend : bool) =
         if add_dependence_edge working_map module_name is_friend
         then ()
         else if !dbg then
           log_issue module_name Errors.Warning_UnboundModuleReference
             (BU.format1 "Unbound module reference %s" (show module_name))
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
         if List.length (ns_of_lid lid) > 0 then
         ignore (enter_namespace original_map working_map (namespace_of_lid lid))
       in

       (*
        * Iterate over the parsing data elements
        *)
       begin
         (auto_open @ pd.elts) |> List.iter (fun elt ->
           match elt with
           | P_begin_module lid -> begin_module lid
           | P_open (b, lid) -> record_open b lid
           | P_implicit_open_module_or_namespace (k, lid) -> record_implicit_open_module_or_namespace (lid, k)
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
  in

  let data_from_cache = filename |> get_parsing_data_from_cache in

  if data_from_cache |> is_some then begin  //we found the parsing data in the checked file
    let deps, has_inline_for_extraction, mo_roots = from_parsing_data (data_from_cache |> must) original_map filename in
    if !dbg then
      BU.print2 "Reading the parsing data for %s from its checked file .. found %s\n" filename (show deps);
    data_from_cache |> must,
    deps, has_inline_for_extraction, mo_roots
  end
  else
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

      let rec collect_module = function
        | Module {no_prelude; mname; decls}
        | Interface {no_prelude; mname; decls} ->
            set_no_prelude no_prelude;
            check_module_declaration_against_filename mname filename;
            add_to_parsing_data (P_begin_module mname);
            collect_decls decls

      and collect_decls decls =
        List.iter (fun x -> collect_decl x.d;
                            List.iter collect_term x.attrs;
                            match x.d with
                            | _ when List.contains Inline_for_extraction x.quals ->
                                add_to_parsing_data P_inline_for_extraction
                            | _ -> ()
                            ) decls

      and collect_decl d =
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
                add_to_parsing_data (P_lid Const.tcclass_lid);
            List.iter collect_tycon ts
            end
        | Exception (_, t) ->
            iter_opt t collect_term
        | NewEffect ed
        | LayeredEffect ed ->
             collect_effect_decl ed

        | Polymonadic_bind (_, _, _, t)
        | Polymonadic_subcomp (_, _, t) -> collect_term t  //collect deps from the effect lids?

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
                (Util.format1 "Automatic dependency analysis demands one module per file (module %s not supported)" (string_of_lid lid true)) 
      and collect_tycon = function
        | TyconAbstract (_, binders, k) ->
            collect_binders binders;
            iter_opt k collect_term
        | TyconAbbrev (_, binders, k, t) ->
            collect_binders binders;
            iter_opt k collect_term;
            collect_term t
        | TyconRecord (_, binders, k, _, identterms) ->
            collect_binders binders;
            iter_opt k collect_term;
            collect_tycon_record identterms
        | TyconVariant (_, binders, k, identterms) ->
            collect_binders binders;
            iter_opt k collect_term;
            List.iter ( function
                      | VpOfNotation t | VpArbitrary t -> collect_term t
                      | VpRecord (record, t) -> collect_tycon_record record;
                                               iter_opt t collect_term
                      ) (List.filter_map Mktuple3?._2 identterms)

      and collect_tycon_record r = 
        List.iter (fun (_, aq, attrs, t) ->
                collect_aqual aq;
                attrs |> List.iter collect_term;
                collect_term t) r

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
        b.battributes |> List.iter collect_term;
        match b with
        | { b = Annotated (_, t) }
        | { b = TAnnotated (_, t) }
        | { b = NoName t } -> collect_term t
        | _ -> ()

      and collect_aqual = function
        | Some (Meta t) -> collect_term t
        | Some TypeClassArg -> add_to_parsing_data (P_lid Const.tcresolve_lid)
        | _ -> ()

      and collect_term t =
        collect_term' t.tm

      and collect_constant = function
        | Const_int (_, Some (Unsigned, Sizet)) ->
            add_to_parsing_data (P_dep (false, ("fstar.sizeT" |> Ident.lid_of_str)))
        | Const_int (_, Some (signedness, width)) ->
            let u = match signedness with | Unsigned -> "u" | Signed -> "" in
            let w = match width with | Int8 -> "8" | Int16 -> "16" | Int32 -> "32" | Int64 -> "64" in
            add_to_parsing_data (P_dep (false, (Util.format2 "fstar.%sint%s" u w |> Ident.lid_of_str)))
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

      and collect_term' = function
        | Wild ->
            ()
        | Const c ->
            collect_constant c
        | Op (_, ts) ->
            List.iter collect_term ts
        | Tvar _
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
                ignore (BU.map_opt attrs_opt (List.iter collect_term));
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
            iter_opt t collect_term;
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
        | Requires (t, _)
        | Ensures (t, _)
        | Labeled (t, _, _) ->
            collect_term t
        | LexList l -> List.iter collect_term l
        | WFOrder (t1, t2) ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.WellFounded")));
          begin
           collect_term t1; collect_term t2
          end
        | Decreases (t, _) -> collect_term t
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

        | IntroImplies(p, q, x, e) ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
          collect_term p;
          collect_term q;
          collect_binder x;
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

        | ElimExists(bs, p, q, b, e) ->
           add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
           collect_binders bs;
           collect_term p;
           collect_term q;
           collect_binder b;
           collect_term e

        | ElimImplies(p, q, e) ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
          collect_term p;
          collect_term q;
          collect_term e

        | ElimAnd(p, q, r, x, y, e) ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
          collect_term p;
          collect_term q;
          collect_term r;
          collect_binder x;
          collect_binder y;
          collect_term e

        | ElimOr(p, q, r, x, e, y, e') ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Classical.Sugar")));
          collect_term p;
          collect_term q;
          collect_term r;
          collect_binder x;
          collect_binder y;
          collect_term e;
          collect_term e'

        | ListLiteral ts ->
          List.iter collect_term ts

        | SeqLiteral ts ->
          add_to_parsing_data (P_dep (false, (Ident.lid_of_str "FStar.Seq.Base")));
          List.iter collect_term ts
        
      and collect_patterns ps =
        List.iter collect_pattern ps

      and collect_pattern p =
        collect_pattern' p.pat

      and collect_pattern' = function
        | PatVar (_, aqual, attrs)
        | PatTvar (_, aqual, attrs)
        | PatWild (aqual, attrs) ->
            collect_aqual aqual;
            attrs |> List.iter collect_term

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


      and collect_branches bs =
        List.iter collect_branch bs

      and collect_branch (pat, t1, t2) =
        collect_pattern pat;
        iter_opt t1 collect_term;
        collect_term t2

      and collect_fieldname fn =
          if nsstr fn <> ""
          then add_to_parsing_data (P_dep (false, lid_of_ids (ns_of_lid fn)))

      in
      let ast, _ = Driver.parse_file filename in
      collect_module ast;
      let pd = !pd in
      let pd = { pd with elts = List.rev pd.elts } in
      let deps, has_inline_for_extraction, mo_roots = from_parsing_data pd original_map filename in
      (* Util.print2 "Deps for %s: %s\n" filename (String.concat " " (!deps)); *)
      pd, deps, has_inline_for_extraction, mo_roots


(* JP: it looks like the code was changed but the comments were never updated.
 * In particular, we no longer compute transitive dependencies, and we no longer
 * map lowercase module names to filenames. *)

// Used by F*.js
let collect_one_cache : ref (SMap.t (list dependence & list dependence & bool)) =
  mk_ref (SMap.create 0)

let set_collect_one_cache (cache: SMap.t (list dependence & list dependence & bool)) : unit =
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
    : list file_name
    & bool =
    let rec all_friend_deps_1
            dep_graph
            (cycle:list file_name)
            (all_friends, all_files)
            filename =
    let dep_node = must (deps_try_find dep_graph filename) in
    match dep_node.color with
    | Gray ->
        failwith "Impossible: cycle detected after cycle detection has passed"
    | Black ->
        (* If the element has been visited already, then the map contains all its
            * dependencies. Otherwise, the map only contains its direct dependencies. *)
        all_friends, all_files
    | White ->
        if !dbg
        then BU.print2 "Visiting %s: direct deps are %s\n"
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
        then BU.print1 "Adding %s\n" filename;
        (* Also build the topological sort (Tarjan's algorithm). *)
        List.collect
          (function | FriendImplementation m -> [m]
                    | d -> [])
         dep_node.edges
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

    let friends, all_files_0 =
        all_friend_deps dep_graph [] ([], []) root_files
    in
    if !dbg
    then BU.print3 "Phase1 complete:\n\t\
                       all_files = %s\n\t\
                       all_friends=%s\n\t\
                       interfaces_with_inlining=%s\n"
                   (String.concat ", " all_files_0)
                   (String.concat ", " (remove_dups (fun x y -> x=y) friends))
                   (String.concat ", " (interfaces_needing_inlining));
    let widened, dep_graph =
        widen_deps friends dep_graph file_system_map widened
    in
    let _, all_files =
        if !dbg
        then BU.print_string "==============Phase2==================\n";
        all_friend_deps dep_graph [] ([], []) root_files
    in
    if !dbg
    then BU.print1 "Phase2 complete: all_files = %s\n" (String.concat ", " all_files);
    all_files,
    widened

let phase1
        file_system_map
        dep_graph
        interfaces_needing_inlining
        for_extraction
=
    if !dbg
    then BU.print_string "==============Phase1==================\n";
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
    : list file_name
    & bool =

    let widened, dep_graph = phase1 file_system_map dep_graph interfaces_needing_inlining for_extraction in
    topological_dependences_of' file_system_map dep_graph interfaces_needing_inlining root_files widened

let all_files_in_include_paths () =
  let paths = Find.full_include_path () in
  List.collect
    (fun path -> 
      let files = safe_readdir_for_include path in
      let files = List.filter (fun f -> Util.ends_with f ".fst" || Util.ends_with f ".fsti") files in
      List.map (fun file -> Filepath.join_paths path file) files)
    paths

(** Collect the dependencies for a list of given files.
    And record the entire dependence graph in the memoized state above **)
(*
 * get_parsing_data_from_cache is a callback passed by caller
 *   to read the parsing data from checked files
 *)
(* In public interface *)
let collect (all_cmd_line_files: list file_name)
            (get_parsing_data_from_cache:string -> option parsing_data)
    : list file_name
    & deps //topologically sorted transitive dependences of all_cmd_line_files
    =
  let all_cmd_line_files =
    match all_cmd_line_files with
    | [] -> all_files_in_include_paths ()
    | _ -> all_cmd_line_files
  in
  let all_cmd_line_files =
      all_cmd_line_files |> List.map (fun fn ->
        match Find.find_file fn with
        | None ->
          raise_error0 Errors.Fatal_ModuleOrFileNotFound
            (Util.format1 "File %s could not be found" fn)
        | Some fn -> fn) in
  (* The dependency graph; keys are lowercased module names, values = list of
   * lowercased module names this file depends on. *)
  let dep_graph : dependence_graph = deps_empty () in

  (* A map from lowercase module names (e.g. [a.b.c]) to the corresponding
   * filenames (e.g. [/where/to/find/A.B.C.fst]). Consider this map
   * immutable from there on. *)
  let file_system_map = build_map all_cmd_line_files in

  let interfaces_needing_inlining = mk_ref [] in
  let add_interface_for_inlining l =
    let l = lowercase_module_name l in
    interfaces_needing_inlining := l :: !interfaces_needing_inlining
  in

  let parse_results = SMap.create 40 in

  (* discover: Do a graph traversal starting from file_name
   *           filling in dep_graph with the dependences *)
  let rec discover_one (file_name:file_name) =
    if deps_try_find dep_graph file_name = None then
    begin
      let parsing_data, (deps, mo_roots, needs_interface_inlining) =
        match SMap.try_find !collect_one_cache file_name with
        | Some cached -> empty_parsing_data, cached
        | None ->
          let parsing_data, deps, needs_interface_inlining, additional_roots = collect_one file_system_map file_name get_parsing_data_from_cache in
          parsing_data, (deps, additional_roots, needs_interface_inlining) in
      if needs_interface_inlining
      then add_interface_for_inlining file_name;
      SMap.add parse_results file_name parsing_data;
      let deps =
          let module_name = lowercase_module_name file_name in
          if is_implementation file_name
          && has_interface file_system_map module_name
          then deps @ [UseInterface module_name]
          else deps
      in
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
  profile (fun () -> List.iter discover_one all_cmd_line_files) "FStarC.Parser.Dep.discover";

  (* At this point, dep_graph has all the (immediate) dependency graph of all the files. *)
  let cycle_detected (dep_graph:dependence_graph) cycle filename =
      let cycle = List.rev cycle in
      Util.print1 "The cycle contains a subset of the modules in:\n  %s \n" (String.concat "\n  `uses` " cycle);

      (* Write the graph to a file for the user to see. *)
      let fn = "dep.graph" in
      with_file_outchannel fn (fun outc -> print_graph outc fn dep_graph file_system_map all_cmd_line_files);

      print_string "\n";
      raise_error0 Errors.Fatal_CyclicDependence [
        text (BU.format1 "Recursive dependency on module %s." filename);
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


    let rec aux (cycle:list file_name) filename =
        let node =
            match deps_try_find dep_graph filename with
            | Some node -> node
            | None ->
              failwith (BU.format1 "Impossible: Failed to find dependencies of %s" filename)
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
              | _ ->
                //if a module A uses B
                //then detect cycles through both B.fsti
                //and B.fst
               [x; UseImplementation f]
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
            then iter_opt
                  (implementation_of_internal file_system_map (lowercase_module_name filename))
                  (fun impl -> if not (List.contains impl all_command_line_files)
                               then mo_files := impl::!mo_files
                               else ())
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

  let inlining_ifaces = !interfaces_needing_inlining in
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
  then BU.print1 "Interfaces needing inlining: %s\n" (String.concat ", " inlining_ifaces);
  all_files,
  mk_deps dep_graph file_system_map all_cmd_line_files all_files inlining_ifaces parse_results

(* In public interface *)
let deps_of deps (f:file_name)
    : list file_name =
    dependences_of deps.file_system_map deps.dep_graph deps.cmd_line_files f

let deps_of_modul deps (m:module_name) : list module_name =
  let aux (fopt:option string) =
    fopt |> BU.map_option (fun f -> f |> deps_of deps |> List.map module_name_of_file)
         |> BU.dflt []
  in
  m |> String.lowercase
    |> SMap.try_find deps.file_system_map
    |> BU.map_option (fun (intf_opt, impl_opt) ->
                      BU.remove_dups (fun x y -> x = y) (aux intf_opt @ aux impl_opt))
    |> BU.dflt []

(* In public interface *)
let print_digest (dig:list (string & string)) : string =
    dig
    |> List.map (fun (m, d) -> BU.format2 "%s:%s" m (BU.base64_encode d))
    |> String.concat "\n"

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

    Deprecated: this will print the dependences among the source files
  *)
let print_make (outc : out_channel) deps : unit =
    let file_system_map = deps.file_system_map in
    let all_cmd_line_files = deps.cmd_line_files in
    let deps = deps.dep_graph in
    let keys = deps_keys deps in
    keys |> List.iter
        (fun f ->
          let dep_node = deps_try_find deps f |> Option.get in
          let files = List.map (file_of_dep file_system_map all_cmd_line_files) dep_node.edges in
          let files = List.map (fun s -> replace_chars s ' ' "\\ ") files in
          //this one prints:
          //   a.fst: b.fst c.fsti a.fsti
          Util.print2 "%s: %s\n\n" f (String.concat " " files))

(* In public interface *)
let print_raw (outc : out_channel) (deps:deps) =
    let (Deps deps) = deps.dep_graph in
      SMap.fold deps (fun k dep_node out ->
        BU.format2 "%s -> [\n\t%s\n] " k (List.map dep_to_string dep_node.edges |> String.concat ";\n\t") :: out) []
      |> String.concat ";;\n"
      |> (fun s -> BU.fprint outc "%s\n" [s])

(** Print the dependencies as returned by [collect] in a Makefile-compatible
    format.

     -- The dependences are among the .checked files

     -- We also print dependences for producing .ml files from .checked files
        This takes care of renaming A.B.C.fst to A_B_C.ml
  *)
let print_full (outc : out_channel) (deps:deps) : unit =
    let pre_tag = Options.Ext.get "dep_pretag" in
    //let (Mk (deps, file_system_map, all_cmd_line_files, all_files)) = deps in
    let sort_output_files (orig_output_file_map:SMap.t string) =
        let order : ref (list string) = mk_ref [] in
        let remaining_output_files = SMap.copy orig_output_file_map in
        let visited_other_modules = SMap.create 41 in
        let should_visit lc_module_name =
            Option.isSome (SMap.try_find remaining_output_files lc_module_name)
            || Option.isNone (SMap.try_find visited_other_modules lc_module_name)
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
        let rec aux = function
            | [] -> ()
            | lc_module_name::modules_to_extract ->
              let visit_file file_opt =
                match file_opt with
                | None -> ()
                | Some file_name ->
                  match deps_try_find deps.dep_graph file_name with
                  | None -> failwith (BU.format2 "Impossible: module %s: %s not found" lc_module_name file_name)
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
    let print_entry (target : string) (all_deps : list string) : unit =
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
    let no_fstar_stubs_file (s:string) : string =
      (* If the original filename begins with FStar.Stubs, then remove that,
      consistent with what extraction will actually do.

      This is VERY IMPORTANT for krml extraction, since we will generate
      the krml file even if we're not extracting these files (they are stubs!)
      per se. Make sure to run karamel tests (or a check-world) if you change this. *)
      let s1 = "FStar.Stubs." in
      let s2 = "FStar." in
      let l1 = String.length s1 in
      if String.length s >= l1 && String.substring s 0 l1 = s1 then
        s2 ^ String.substring s l1 (String.length s - l1)
      else
        s
    in
    let output_file ext fst_file =
        let basename = Option.get (check_and_strip_suffix (Filepath.basename fst_file)) in
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
            let dep_node = deps_try_find deps.dep_graph file_name |> Option.get in
            let iface_fn, iface_deps =
                if is_interface file_name
                then None, None
                else match interface_of deps (lowercase_module_name file_name) with
                     | None ->
                       None, None
                     | Some iface ->
                       Some iface,
                       Some ((Option.get (deps_try_find deps.dep_graph iface)).edges)
            in
            let iface_deps =
                BU.map_opt iface_deps
                           (List.filter
                             (fun iface_dep ->
                                not (BU.for_some (dep_subsumed_by iface_dep) dep_node.edges)))
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
                  BU.remove_dups (fun x y -> x = y) (files @ iface_files)
            in

            (*
             * AR: depend on A.fsti.checked, rather than A.fsti
             *     see #1919
             *)
            let files =
              if iface_fn |> is_some then
                let iface_fn = iface_fn |> must in
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
                   BU.remove_dups (fun x y -> x = y) (fst_files @ fst_files_from_iface),
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
                           lowercase_module_name df <> lowercase_module_name file_name //avoid circular deps on f's own cmx
                           && Options.should_extract (lowercase_module_name df) Options.OCaml)
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
             (BU.format1 "Interface %s is admitted without an implementation" (module_name_of_file fsti)));
    print_all "ALL_FST_FILES" all_fst_files;
    print_all "ALL_FSTI_FILES" all_fsti_files;
    print_all "ALL_CHECKED_FILES" all_checked_files;
    print_all "ALL_FS_FILES" all_fs_files;
    print_all "ALL_ML_FILES" all_ml_files;
    print_all "ALL_KRML_FILES" all_krml_files;

    FStarC.StringBuffer.output_channel outc sb

let do_print (outc : out_channel) (fn : string) deps : unit =
  let pref () =
    BU.fprint outc "# This .depend was generated by F* %s\n" [!Options._version];
    BU.fprint outc "# Executable: %s\n" [show BU.exec_name];
    BU.fprint outc "# Hash: %s\n" [!Options._commit];
    BU.fprint outc "# Running in directory %s\n" [show (Filepath.normalize_file_path (BU.getcwd ()))];
    BU.fprint outc "# Command line arguments: \"%s\"\n" [show (BU.get_cmd_args ())];
    BU.fprint outc "\n" [];
    ()
  in
  match Options.dep() with
  | Some "make" ->
      pref ();
      print_make outc deps
  | Some "full" ->
      pref ();
      profile (fun () -> print_full outc deps) "FStarC.Parser.Deps.print_full_deps"
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
    deps.all_files |> BU.for_some (fun f ->
        is_implementation f
        && String.lowercase (module_name_of_file f) = m)

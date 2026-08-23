(*
   Copyright 2008-2024 Microsoft Research

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
module FStarC.Find

open FStarC
open FStarC.Effect
open FStar.List.Tot
module BU = FStarC.Util

open FStarC.Class.Show

let cached_fun #a (cache : SMap.t a) (f : string -> ML a) : string -> ML a =
  fun s ->
    match SMap.try_find cache s with
    | Some v -> v
    | None ->
      let v = f s in
      SMap.add cache s v;
      v

(* caches *)
let _full_include : ref (option (list string)) = mk_ref None
let _module_include_paths_normalized : ref (option (list module_include_path)) = mk_ref None
let find_file_cache : SMap.t (option string) = SMap.create 100

(* Bumped every time the include path (or anything else affecting file
resolution) changes. Clients that cache results derived from the include path
can use this to invalidate their own caches. *)
let _epoch : ref int = mk_ref 0

let clear () : ML unit =
  SMap.clear find_file_cache;
  _full_include := None;
  _module_include_paths_normalized := None;
  _epoch := !_epoch + 1;
  ()

(* Internal state, settable with the functions exposed in the interface. *)
let _include : ref (list string) = mk_ref []
let _file_list : ref (list string) = mk_ref []
let _cache_dir : ref (option string) = mk_ref None
let _odir : ref (option string) = mk_ref None
let _no_default_includes : ref bool = mk_ref false
let _with_fstarc : ref bool = mk_ref false

let get_include_path () : ML (list string) = !_include
let set_include_path (path : list string) : ML unit =
  clear ();
  _include := path

let set_file_list (files : list string) : ML unit =
  clear ();
  _file_list := files

let get_cache_dir () : ML (option string) = !_cache_dir
let set_cache_dir (path : string) : ML unit =
  clear ();
  _cache_dir := Some path

let get_odir () : ML (option string) = !_odir
let set_odir (path : string) : ML unit =
  clear ();
  _odir := Some path

let get_no_default_includes () : ML bool = !_no_default_includes
let set_no_default_includes (b : bool) : ML unit =
  clear ();
  _no_default_includes := b

let get_with_fstarc () : ML bool = !_with_fstarc
let set_with_fstarc (b : bool) : ML unit =
  clear ();
  _with_fstarc := b

let fstar_bin_directory : string =
  BU.get_exec_dir ()

let lib_root () : ML (option string) =
  (* No default includes means we don't try to find a library on our own. *)
  if !_no_default_includes then
    None
  else
    (* FSTAR_LIB can be set in the environment to override the library *)
    match Util.expand_environment_variable "FSTAR_LIB" with
    | Some s -> Some s
    | None ->
      (* Otherwise, just at the default location *)
      Some (Filepath.canonicalize <| fstar_bin_directory ^ "/../lib/fstar")

let read_fstar_include (fn : string) : ML (option (list string)) =
  try
    let s = BU.file_get_contents fn in
    let subdirs =
      // Read each line
      String.split ['\r'; '\n'] s |>
      // Trim whitespace. NOTE: Carriage returns (\r) should be trimmed
      // by BU.trim_string (which is BatString.trim) according to
      // the docs, but do not seem to be. So instead we use it as a
      // separator above and just get a few more empty lines.
      List.map BU.trim_string |>
      // And keep the non-empty lines that don't begin with '#'
      List.filter (fun s -> s <> "" && not (String.get s 0 = '#'))
    in
    Some subdirs
  with
  | _ ->
    failwith ("Could not read " ^ fn);
    None

let has_fstar_include (dirname:string) : ML bool =
  Filepath.file_exists (dirname ^ "/fstar.include")

let rec expand_include_d (dirname : string) : ML (list string) =
  if has_fstar_include dirname then (
    let dot_inc_path = dirname ^ "/fstar.include" in
    let subdirs = Some?.v <| read_fstar_include dot_inc_path in
    dirname :: List.collect (fun subd -> expand_include_d (dirname ^ "/" ^ subd)) subdirs
  ) else
    [dirname]

let expand_include_ds (dirnames : list string) : ML (list string) =
  List.collect expand_include_d dirnames

let recursive_include_d (dirname:string) : ML (list string) =
  expand_include_d dirname |> List.filter (fun d -> not (has_fstar_include d))

let recursive_manifest_include_d (dirname:string) : ML (list string) =
  match expand_include_d dirname with
  | _::paths -> paths |> List.filter (fun d -> not (has_fstar_include d))
  | [] -> []

let fstarc_roots () : ML (list string) =
  if !_with_fstarc
  then [Filepath.canonicalize <| fstar_bin_directory ^ "/../lib/fstar/fstarc"]
  else []

let lib_roots () : ML (list string) =
  Common.option_to_list (lib_root ()) @ fstarc_roots ()

let lib_paths () : ML (list string) =
  lib_roots () |> expand_include_ds

let rec path_is_at_or_below (root:string) (path:string) : ML bool =
  if root = path then true
  else
    let parent = Filepath.dirname path in
    parent <> path && path_is_at_or_below root parent

(* Add command-line file parents not already owned by an explicit root as flat
  roots. Roots declared by their [fstar.include] are flat too. For example, when running:
  > fstar.exe test/Test01.fst
  we add `test` as an include path under the assumption that the file defines the Test01 module. *)
let command_line_include_roots () : ML (list string) =
  match !_file_list with
  | [] -> []
  | files ->
    let explicit_roots =
      !_include |> expand_include_ds |> List.map Filepath.normalize_file_path
    in
    let recursive_explicit_roots =
      !_include |> List.collect recursive_include_d |> List.map Filepath.normalize_file_path
    in
    let cwd = Filepath.normalize_file_path (Filepath.getcwd ()) in
    let file_roots =
      List.fold_left (fun roots file ->
        let root = Filepath.normalize_file_path (Filepath.dirname file) in
        let is_file = Filepath.file_exists file && not (Filepath.is_directory file) in
        (* Nonexistent entries may be unsaved files supplied through the IDE VFS,
          but synthetic paths outside cwd must not introduce broad include roots. *)
        if is_file || (not (Filepath.file_exists file) && path_is_at_or_below cwd root) then
          if List.contains root roots then roots else roots @ [root]
        else roots)
        [] files
    in
    file_roots
    |> List.filter (fun root ->
        not (List.contains root explicit_roots
          || List.existsb (fun explicit_root ->
            path_is_at_or_below explicit_root root) recursive_explicit_roots))

let command_line_include_paths () : ML (list string) =
  command_line_include_roots () |> expand_include_ds

let epoch () : ML int = !_epoch

let full_include_path () : ML _ =
  // Stats.record "Find.full_include_path" fun () ->
  match !_full_include with
  | Some paths -> paths
  | None ->
    let res =
      let cache_dir =
        match !_cache_dir with
        | None -> []
        | Some c -> [c]
      in
      let include_paths = !_include |> expand_include_ds in
      cache_dir @ lib_paths () @ include_paths @ command_line_include_paths ()
      @ expand_include_d "."
    in
    _full_include := Some res;
    res

let module_include_paths_normalized () : ML (list module_include_path) =
  match !_module_include_paths_normalized with
  | Some paths -> paths
  | None ->
    let recursive_dirs =
      ((!_include |> List.collect recursive_include_d)
       @ ((lib_roots () @ command_line_include_roots () @ ["."])
          |> List.collect recursive_manifest_include_d))
      |> List.map Filepath.normalize_file_path
    in
    let paths =
      full_include_path ()
      |> List.map (fun dir ->
        let dir = Filepath.normalize_file_path dir in
        { dir; prefix=if List.contains dir recursive_dirs then Some [] else None })
    in
    _module_include_paths_normalized := Some paths;
    paths

let do_find (paths : list string) (filename : string) : ML (option string) =
  // Stats.record "Find.do_find" fun () ->
  if Filepath.is_path_absolute filename then
    if Filepath.file_exists filename then
      Some filename
    else
      None
  else
  try
      (* In reverse, because the last directory has the highest precedence. *)
      (* FIXME: We should fail if we find two files with the same name *)
      BU.find_map (List.rev paths) (fun p ->
        let path =
          if p = "." then filename
          else Filepath.join_paths p filename in
        if Filepath.file_exists path then
          Some path
        else
          None)
  with
  | _ -> None
  // ^ to deal with issues like passing bogus strings as paths like " input"

(* Note: eta important below. *)
let find_file =
  cached_fun find_file_cache fun s ->
    do_find (full_include_path ()) s

let find_file_odir =
  (* NOTE: this function is not cached, since the plugin-building code
  will sometimes see a cmxs does not exist and then try to build it and load it,
  so we should not cache a None result. However this is such a cold path that
  it doesn't matter at all, so just drop the cache altogether. *)
  // cached_fun find_file_odir_cache
  fun s ->
    let odir = match !_odir with Some d -> [d] | None -> [] in
    do_find (full_include_path () @ odir) s

let prepend_cache_dir fpath : ML _ =
  match !_cache_dir with
  | None -> fpath
  | Some x -> Filepath.join_paths x (Filepath.basename fpath)

let prepend_output_dir fname : ML _ =
  match !_odir with
  | None -> fname
  | Some x -> Filepath.join_paths x fname

let locate () : ML _ =
  Util.get_exec_dir () |> Filepath.normalize_file_path

let locate_lib () : ML _ =
  Option.map Filepath.normalize_file_path (lib_root ())

let locate_ocaml () : ML _ =
  // This is correct right now, but probably should change.
  Util.get_exec_dir () ^ "/../lib" |> Filepath.normalize_file_path


(* When reading checked files, we could obtain ranges where the
filepath does not make sense any more. For instance if we check
`a/A.fst`, and then go into `a/` and check `B.fst`, the ranges
in `A.fst.checked` will still refer to `a/A.fst`, which is not
a valid path. To palliate this, we
  1) just take the basename (ignore the path completely); and
  2) try to find this file in our include path.

This function is called by error reporting (both batch and IDE). *)
let refind_file (f:string) : ML string =
  try
    match find_file (Filepath.basename f) with
    | None -> f // Couldn't find file; just return the original path
    | Some abs -> abs
  with _ -> f

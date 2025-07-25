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

let cached_fun #a (cache : SMap.t a) (f : string -> a) : string -> a =
  fun s ->
    match SMap.try_find cache s with
    | Some v -> v
    | None ->
      let v = f s in
      SMap.add cache s v;
      v

(* caches *)
let _full_include : ref (option (list string)) = mk_ref None
let find_file_cache : SMap.t (option string) = SMap.create 100

let clear () =
  SMap.clear find_file_cache;
  _full_include := None;
  ()

(* Internal state, settable with the functions exposed in the interface. *)
let _include : ref (list string) = mk_ref []
let _cache_dir : ref (option string) = mk_ref None
let _odir : ref (option string) = mk_ref None
let _no_default_includes : ref bool = mk_ref false
let _with_fstarc : ref bool = mk_ref false

let get_include_path () : list string = !_include
let set_include_path (path : list string) : unit =
  clear ();
  _include := path

let get_cache_dir () : option string = !_cache_dir
let set_cache_dir (path : string) : unit =
  clear ();
  _cache_dir := Some path

let get_odir () : option string = !_odir
let set_odir (path : string) : unit =
  clear ();
  _odir := Some path

let get_no_default_includes () : bool = !_no_default_includes
let set_no_default_includes (b : bool) : unit =
  clear ();
  _no_default_includes := b

let get_with_fstarc () : bool = !_with_fstarc
let set_with_fstarc (b : bool) : unit =
  clear ();
  _with_fstarc := b

let fstar_bin_directory : string =
  BU.get_exec_dir ()

let read_fstar_include (fn : string) : option (list string) =
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

let rec expand_include_d (dirname : string) : list string =
  let dot_inc_path = dirname ^ "/fstar.include" in
  if Filepath.file_exists dot_inc_path then (
    let subdirs = Some?.v <| read_fstar_include dot_inc_path in
    dirname :: List.collect (fun subd -> expand_include_d (dirname ^ "/" ^ subd)) subdirs
  ) else
    [dirname]

let expand_include_ds (dirnames : list string) : list string =
  List.collect expand_include_d dirnames

let lib_root () : option string =
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

let fstarc_paths () =
  if !_with_fstarc
  then expand_include_d (Filepath.canonicalize <| fstar_bin_directory ^ "/../lib/fstar/fstarc")
  else []

let lib_paths () =
  (Common.option_to_list (lib_root ()) |> expand_include_ds)
  @ fstarc_paths ()

let full_include_path () =
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
      cache_dir @ lib_paths () @ include_paths @ expand_include_d "."
    in
    _full_include := Some res;
    res

let do_find (paths : list string) (filename : string) : option string =
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

let prepend_output_dir fname =
  match !_odir with
  | None -> fname
  | Some x -> Filepath.join_paths x fname

let prepend_cache_dir fpath =
  match !_cache_dir with
  | None -> fpath
  | Some x -> Filepath.join_paths x (Filepath.basename fpath)

let locate () =
  Util.get_exec_dir () |> Filepath.normalize_file_path

let locate_lib () =
  Option.map Filepath.normalize_file_path (lib_root ())

let locate_ocaml () =
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
let refind_file (f:string) : string =
  try
    match find_file (Filepath.basename f) with
    | None -> f // Couldn't find file; just return the original path
    | Some abs -> abs
  with _ -> f

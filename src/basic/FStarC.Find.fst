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

open FStar
open FStarC.Compiler
open FStarC.Compiler.Effect
open FStarC.Compiler.List
module BU = FStarC.Compiler.Util

let fstar_bin_directory : string =
  BU.get_exec_dir ()

let read_fstar_include (fn : string) : option (list string) =
  try
    let s = BU.file_get_contents fn in
    let subdirs = String.split ['\n'] s |> List.filter (fun s -> s <> "" && not (String.get s 0 = '#')) in
    Some subdirs
  with
  | _ ->
    failwith ("Could not read " ^ fn);
    None

let rec expand_include_d (dirname : string) : list string =
  let dot_inc_path = dirname ^ "/fstar.include" in
  if Util.file_exists dot_inc_path then (
    let subdirs = Some?.v <| read_fstar_include dot_inc_path in
    dirname :: List.collect (fun subd -> expand_include_d (dirname ^ "/" ^ subd)) subdirs
  ) else
    [dirname]

let expand_include_ds (dirnames : list string) : list string =
  List.collect expand_include_d dirnames

(* TODO: normalize these paths. This will probably affect makefiles since
make does not normalize the paths itself. Also, move this whole logic away
from this module. *)
let lib_root () : option string =
  (* No default includes means we don't try to find a library on our own. *)
  if Options.no_default_includes() then
    None
  else
    (* FSTAR_LIB can be set in the environment to override the library *)
    match Util.expand_environment_variable "FSTAR_LIB" with
    | Some s -> Some s
    | None ->
      (* Otherwise, try to find the library in the default locations. It's ulib/
      in the repository, and lib/fstar/ in the binary package. *)
      if Util.file_exists (fstar_bin_directory ^ "/../ulib")
      then Some (fstar_bin_directory ^ "/../ulib")
      else if Util.file_exists (fstar_bin_directory ^ "/../lib/fstar")
      then Some (fstar_bin_directory ^ "/../lib/fstar")
      else None

let lib_paths () =
  Common.option_to_list (lib_root ()) |> expand_include_ds

let include_path () =
  let cache_dir =
    match Options.cache_dir() with
    | None -> []
    | Some c -> [c]
  in
  let include_paths =
    Options.include_ () |> expand_include_ds
  in
  cache_dir @ lib_paths () @ include_paths @ expand_include_d "."

let find_file =
  let file_map = BU.smap_create 100 in
  fun filename ->
     match BU.smap_try_find file_map filename with
     | Some f -> f
     | None ->
       let result =
          (try
              if BU.is_path_absolute filename then
                if BU.file_exists filename then
                  Some filename
                else
                  None
              else
                (* In reverse, because the last directory has the highest precedence. *)
                BU.find_map (List.rev (include_path ())) (fun p ->
                  let path =
                    if p = "." then filename
                    else BU.join_paths p filename in
                  if BU.file_exists path then
                    Some path
                  else
                    None)
           with | _ -> //to deal with issues like passing bogus strings as paths like " input"
                  None)
       in
       if Some? result
       then BU.smap_add file_map filename result;
       result


let prepend_output_dir fname =
  match Options.output_dir () with
  | None -> fname
  | Some x -> Util.join_paths x fname

let prepend_cache_dir fpath =
  match Options.cache_dir () with
  | None -> fpath
  | Some x -> Util.join_paths x (Util.basename fpath)

let locate () =
  Util.get_exec_dir () |> Util.normalize_file_path

let locate_lib () =
  BU.map_opt (lib_root ()) Util.normalize_file_path

let locate_ocaml () =
  // This is correct right now, but probably should change.
  Util.get_exec_dir () ^ "/../lib" |> Util.normalize_file_path

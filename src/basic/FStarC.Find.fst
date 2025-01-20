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
open FStarC
open FStarC
open FStarC.Effect
open FStarC.List
module BU = FStarC.Util
open FStarC.Class.Show

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
      (* Otherwise, just at the default location *)
      Some (fstar_bin_directory ^ "/../lib/fstar")

let fstarc_paths () =
  if Options.with_fstarc ()
  then expand_include_d (fstar_bin_directory ^ "/../lib/fstar/fstarc")
  else []

let lib_paths () =
  (Common.option_to_list (lib_root ()) |> expand_include_ds)
  @ fstarc_paths ()

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

let do_find (paths : list string) (filename : string) : option string =
  if BU.is_path_absolute filename then
    if BU.file_exists filename then
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
          else BU.join_paths p filename in
        if BU.file_exists path then
          Some path
        else
          None)
  with
    | _ -> None
    // ^ to deal with issues like passing bogus strings as paths like " input"

let find_file =
  let cache = BU.smap_create 100 in
  fun filename ->
     match BU.smap_try_find cache filename with
     | Some f -> f
     | None ->
       let result = do_find (include_path ()) filename in
       if Some? result
       then BU.smap_add cache filename result;
       result

let find_file_odir =
  let cache = BU.smap_create 100 in
  fun filename ->
     match BU.smap_try_find cache filename with
     | Some f -> f
     | None ->
       let odir = match Options.output_dir () with Some d -> [d] | None -> [] in
       let result = do_find (include_path () @ odir) filename in
       if Some? result
       then BU.smap_add cache filename result;
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

let z3url = "https://github.com/Z3Prover/z3/releases"

let packaged_z3_versions = ["4.8.5"; "4.13.3"]

let z3_install_suggestion (v : string) : list Pprint.document =
  let open FStarC.Errors.Msg in
  let open FStarC.Pprint in
  [
    prefix 4 1 (text <| BU.format1 "Please download version %s of Z3 from" v)
              (url z3url) ^/^
      group (text "and install it into your $PATH as" ^/^ squotes
        (doc_of_string (Platform.exe ("z3-" ^ v))) ^^ dot);
    if List.mem v packaged_z3_versions then
      text <| BU.format1 "Version %s of Z3 should be included in binary packages \
              of F*. If you are using a binary package and are seeing
              this error, please file a bug report." v
    else
      empty
  ]

(* Check if [path] is potentially a valid z3, by trying to run
it with -version and checking for non-empty output. Alternatively
we could call [which] on it (if it's not an absolute path), but
we shouldn't rely on the existence of a binary which. *)
let z3_inpath (path:string) : bool =
  try
    let s = BU.run_process "z3_pathtest" path ["-version"] None in
    s <> ""
  with
  | _ -> false

(* Find the Z3 executable that we should invoke for a given version.

- If the user provided the --smt option, use that binary unconditionally.
- We then look in $LIB/z3-VER/z3, where LIB is the F* library root, for example
  /usr/local/lib/fstar/z3-4.8.5/bin/z3, for an installed package. We ship Z3 4.8.5
  and 4.13.3 in the binary package in these paths, so F* automatically find them
  without relying on PATH or adding more stuff to the user's /usr/local/bin.
  Each $PREFIX/lib/fstar/z3-VER directory roughly contains an extracted Z3
  binary package, but with many files removed (currently we just keep LICENSE
  and the executable).

- Else we check the PATH:
  - If z3-VER (or z3-VER.exe) exists in the PATH use it.
  - Otherwise, default to "z3" in the PATH.

We cache the chosen executable for every Z3 version we've ran.
*)
let do_locate_z3 (v:string) : option string =
  let open FStarC.Class.Monad in
  let guard (b:bool) : option unit = if b then Some () else None in
  let (<|>) o1 o2 () =
    match o1 () with
    | Some v -> Some v
    | None -> o2 ()
  in
  let path =
    let in_lib () : option string =
      let! root = lib_root () in
      let path = Platform.exe (root ^ "/z3-" ^ v ^ "/bin/z3") in
      let path = BU.normalize_file_path path in
      guard (BU.file_exists path);!
      Some path
    in
    let from_path (cmd : string) () =
      let cmd = Platform.exe cmd in
      guard (z3_inpath cmd);!
      Some cmd
    in
    (Options.smt <|>
    in_lib <|>
    from_path ("z3-" ^ v) <|>
    from_path "z3" <|> (fun _ -> None)) ()
  in
  if Debug.any () then
    BU.print2 "do_locate_z3(%s) = %s\n" (Class.Show.show v) (Class.Show.show path);
  path

let locate_z3 (v : string) : option string =
  let cache : BU.smap (option string) = BU.smap_create 5 in
  let find_or (k:string) (f : string -> option string) : option string =
    match BU.smap_try_find cache k with
    | Some v -> v
    | None ->
      let v = f k in
      BU.smap_add cache k v;
      v
  in
  find_or v do_locate_z3

(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Filepath

open FStarC.Effect
module I = FStarC.SmallInt
module S = FStarC.String

[@@custard_extern "(fun fn -> snd (BatString.rsplit fn \".\"))"]
let get_file_extension _ = admit ()

[@@custard_extern "(fun path_str -> let module P = BatPathGen.OfString in P.is_absolute (P.of_string path_str))"]
private assume val is_absolute_posix : string -> bool

private
let is_ascii_letter (c:I.t) : bool =
  I.((c >= of_char 'a' && c <= of_char 'z') || (c >= of_char 'A' && c <= of_char 'Z'))

(* NOTE: Working around https://github.com/ocaml-batteries-team/batteries-included/issues/1136 *)
private
let is_absolute_windows (s:string) : bool =
  FStarC.Platform.windows &&
  (S.byte_at s I.zero = I.of_char '\\' ||
   (is_ascii_letter (S.byte_at s I.zero) &&
    S.byte_at s I.one = I.of_char ':' &&
    S.byte_at s (I.of_int 2) = I.of_char '\\'))

let is_path_absolute s = is_absolute_posix s || is_absolute_windows s

[@@custard_extern "(fun path_str0 path_str1 -> let module P = BatPathGen.OfString in P.to_string (P.Operators.(//@) (P.of_string path_str0) (P.of_string path_str1)))"]
let join_paths _ _ = admit ()

[@@custard_extern "(==)"]
private assume val phys_eq (#a:Type) : a -> a -> bool

[@@custard_extern "(fun f -> f ())"]
private assume val run_tot (#a:Type) : (unit -> ML a) -> a

[@@custard_extern "Filename.basename"]
private assume val filename_basename : string -> string

(* Called for every range; remember the last result *)
private
let last_basename : ref (string & string) = mk_ref ("", "")

let basename s =
  run_tot (fun () ->
    let (s', b) = !last_basename in
    if phys_eq s s' then b
    else (let b = filename_basename s in last_basename := (s, b); b))

[@@custard_extern "Filename.dirname"]
let dirname _ = admit ()

[@@custard_extern "Sys.getcwd"]
let getcwd _ = admit ()

[@@custard_extern "(fun dir -> Array.to_list (Sys.readdir dir))"]
let readdir _ = admit ()

[@@custard_extern "(fun f g -> let a = Unix.stat f and b = Unix.stat g in a.Unix.st_dev = b.Unix.st_dev && a.Unix.st_ino = b.Unix.st_ino)"]
let paths_to_same_file _ _ = admit ()

[@@custard_extern "Sys.file_exists"]
let file_exists _ = admit ()

(* NB: Sys.is_directory raises Sys_error if the path does not exist. We catch
   it instead of testing existence first, to only do a single stat. *)
[@@custard_extern "(fun f -> try Sys.is_directory f with Sys_error _ -> false)"]
let is_directory _ = admit ()

[@@custard_extern "(fun path_str -> let module P = BatPathGen.OfString in P.to_string (P.normalize_in_tree (P.of_string path_str)))"]
let canonicalize _ = admit ()

(* The cwd never changes during a run of F* (we never call chdir), so we
   cache it: normalize_file_path is called very often on relative paths. *)
private
let cwd_cache : ref (option string) = mk_ref None

private
let cached_getcwd () : ML string =
  match !cwd_cache with
  | Some cwd -> cwd
  | None ->
    let cwd = getcwd () in
    cwd_cache := Some cwd;
    cwd

let normalize_file_path s =
  if is_path_absolute s then canonicalize s
  else canonicalize (join_paths (cached_getcwd ()) s)

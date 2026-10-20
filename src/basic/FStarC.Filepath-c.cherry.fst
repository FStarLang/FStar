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

(* The Cherry implementation.  The OCaml one uses Batteries' BatPathGen for
   paths, whose behaviour this follows: a path is absolute if it is empty or
   starts with '/', empty components are dropped, and normalizing it in a
   tree removes '.' components and resolves '..' ones lexically. *)

open FStarC.Effect
module I = FStarC.SmallInt
module S = FStarC.String

(* In ulib/c/cherry.c. *)
[@@custard_extern "cherry_io_error"]
private assume val io_error : unit -> ML string
[@@custard_extern "cherry_basename"]
private assume val c_basename : string -> string
[@@custard_extern "cherry_dirname"]
private assume val c_dirname : string -> string
[@@custard_extern "cherry_getcwd"]
private assume val c_getcwd : unit -> ML string
[@@custard_extern "cherry_readdir"]
private assume val c_readdir : string -> ML string
[@@custard_extern "cherry_same_file"]
private assume val c_same_file : string -> string -> ML bool
[@@custard_extern "cherry_file_exists"]
private assume val c_file_exists : string -> bool
[@@custard_extern "cherry_is_directory"]
private assume val c_is_directory : string -> bool

(* Raises the error the last external recorded, if any. *)
private let check () : ML unit =
  let e = io_error () in
  if e <> "" then failwith e

(* What follows the last '.', and "" if there is none (where OCaml raises
   Not_found). *)
let get_file_extension fn =
  let rec last (l:list string) : string =
    match l with
    | [] | [_] -> ""
    | [_; x] -> x
    | _ :: l -> last l in
  last (S.split_on_string fn ".")

private
let is_absolute_posix (s:string) : bool =
  s = "" || S.byte_at s I.zero = I.of_char '/'

(* The OCaml implementation also accepts Windows' absolute paths on Windows;
   Cherry's runtime is POSIX only (FStarC.Platform.Base.system is Unix). *)
let is_path_absolute s = is_absolute_posix s

(* The components of a path, without the empty ones. *)
private
let components (s:string) : list string =
  List.Tot.filter (fun c -> c <> "") (S.split_on_string s "/")

private
let path_to_string (absolute:bool) (cs:list string) : string =
  if absolute then "/" ^ S.concat "/" cs
  else if Nil? cs then "."
  else S.concat "/" cs

(* An absolute [q] is the result on its own (where OCaml raises
   Invalid_argument). *)
let join_paths p q =
  if is_absolute_posix q then path_to_string true (components q)
  else path_to_string (is_absolute_posix p) (List.Tot.append (components p) (components q))

let basename s = c_basename s

let dirname s = c_dirname s

let getcwd () =
  let s = c_getcwd () in
  check ();
  s

let readdir dir =
  let entries = c_readdir dir in
  check ();
  if entries = "" then []
  else S.split_on_string entries "\x00"

let paths_to_same_file f g =
  let r = c_same_file f g in
  check ();
  r

let file_exists f = c_file_exists f

let is_directory f = c_is_directory f

(* [rev_out] is the normalized prefix, reversed; it starts with a '..' only
   if all of it is.  A '..' above the root is the root, as in POSIX (where
   OCaml raises Malformed_path). *)
private
let rec normalize (absolute:bool) (rev_out cs:list string) : Tot (list string) (decreases cs) =
  match cs with
  | [] -> List.Tot.rev rev_out
  | "." :: cs -> normalize absolute rev_out cs
  | ".." :: cs ->
    (match rev_out with
     | c :: rev_out' when c <> ".." -> normalize absolute rev_out' cs
     | _ ->
       if absolute then normalize absolute rev_out cs
       else normalize absolute (".." :: rev_out) cs)
  | c :: cs -> normalize absolute (c :: rev_out) cs

let canonicalize s =
  let absolute = is_absolute_posix s in
  path_to_string absolute (normalize absolute [] (components s))

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

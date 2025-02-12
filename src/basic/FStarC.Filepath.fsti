(*
   Copyright 2008-2025 Nikhil Swamy and Microsoft Research

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

val get_file_extension: string -> string
val is_path_absolute: string -> bool
val join_paths: string -> string -> string
val basename: string -> string (* name of file without directory *)
val dirname : string -> string
val getcwd: unit -> string
val readdir: string -> list string
val paths_to_same_file: string -> string -> bool

val file_exists: string -> Tot bool
val is_directory: string -> Tot bool

(* Remove /../ and /./ components from a path. Result is absolute or relative
according to input. *)
val canonicalize : string -> string

(* Like canonicalize, but always returns an absolute path. *)
val normalize_file_path: string -> string

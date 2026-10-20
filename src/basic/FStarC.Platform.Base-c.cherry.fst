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
module FStarC.Platform.Base

(* The Cherry implementation.  The C runtime is POSIX only. *)

open FStarC.Effect

let system = Unix

(* In ulib/c/cherry.c: uname(2)'s sysname, which is what the uname command
   prints, or "Unix" (OCaml's Sys.os_type) if it fails. *)
[@@custard_extern "cherry_uname"]
private assume val c_uname : unit -> ML string

let kernel () = c_uname ()

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

open FStarC.Effect

[@@custard_extern "Sys.os_type"]
private assume val os_type : string

(* OCaml documents these three as the only values of [Sys.os_type]. *)
let system =
  match os_type with
  | "Win32" -> Win32
  | "Cygwin" -> Cygwin
  | _ -> Unix

[@@custard_extern "(fun () -> try List.hd (Process.read_stdout \"uname\" [| |]) with _ -> Sys.os_type)"]
let kernel _ = admit ()

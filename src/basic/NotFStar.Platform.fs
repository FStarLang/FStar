(*
   Copyright 2008-2018 Microsoft Research

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
﻿#light "off"

module FStar.Platform

open FStar
open System

type sys =
| Windows
| Posix

let system : sys =
    match Environment.OSVersion.Platform with
    | PlatformID.MacOSX
    | PlatformID.Unix -> Posix
    | _ -> Windows

let exe (name : string) =
    match system with
    | Windows -> Util.format1 "%s.exe" name
    | Posix   -> name

let is_fstar_compiler_using_ocaml = false


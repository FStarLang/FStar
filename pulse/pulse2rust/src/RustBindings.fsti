(*
   Copyright 2023 Microsoft Research

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

module RustBindings

open FStarC.Compiler.Effect

open Pulse2Rust.Rust.Syntax

// val i64 : Type0

// val one : i64

// val add_2 (x:i64) : string

// val dflt (x:option i64) : string

val file_to_rust (f:file) : string
val fn_to_string (f:fn) : string
val expr_to_string (e:expr) : string
val typ_to_string (t:typ) : string
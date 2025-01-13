(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
module FStarC.Hooks

open FStarC.Compiler.Effect

(* This function sets ties some know between modules in the compiler source tree,
enabling more recursion and breaking some dependencies.

This is called directly by the Javascript port (it doesn't call Main) and the ocaml tests. *)
val setup_hooks () : unit

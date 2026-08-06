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

(** The OCaml backend for Custard.

    Custard produces a *whole program*, so unlike the ML extraction this emits
    a single flat OCaml module in which every definition has a mangled global
    name.  Symbols with no F* definition ([DExternal]) are bound to the
    corresponding value of the existing F* OCaml support library, so that the
    hand-written realizations in [ulib/ml] keep working. *)
module FStarC.Custard.PrintOCaml

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

(** The OCaml identifier a Custard name is emitted under. *)
val ocaml_value_name : name -> ML string
val ocaml_type_name  : name -> ML string

val print_program : program -> ML string

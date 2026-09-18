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

(** Section 122.  The F\# backend for Custard, targeting .NET 10.

    F\# is an ML, so the shape of the output is the OCaml backend's: one flat
    module, every definition under a mangled global name, no functors and no
    signatures.  What it is *not* is the OCaml backend with the syntax
    changed.  The OCaml backend spends most of its effort binding names to
    the hand-written realizations in [ulib/ml] -- a machine integer is
    [FStar_UInt32.t], an addition is [FStar_UInt32.add] -- because OCaml has
    no unsigned 32-bit type to compile to.  .NET has all of them, and a real
    binary32, and a 128-bit integer.  So this backend compiles the way the
    direct-to-C backend compiles: natively, to the target's own types and
    operators, with no support library between the program and the machine.

    That decides which programs it accepts.  It is the ones the C backend
    accepts -- Low\*, Pulse, EverParse -- and not the ones the OCaml backend
    accepts, because those reach the [ulib/ml] realizations and there is no
    F\# equivalent of them.  A program that does is refused by name
    (section 122.9) rather than compiled into a reference to something that
    does not exist. *)
module FStarC.Custard.PrintFSharp

open FStarC
open FStarC.Effect
open FStarC.Custard.Syntax

(** The F\# identifier a Custard name is emitted under. *)
val fsharp_value_name : name -> ML string
val fsharp_type_name  : name -> ML string

(** The F\# module the generated source declares, which is also the base name
    of the file it is written to. *)
val module_name_of_unit : string -> ML string

(** The program as F\# source.  [stem] is the base name of the output file,
    which is what the module is named after. *)
val print_program : string -> program -> ML string

(** The [.fsproj] that builds {!print_program}'s output, and the support
    library it lists ahead of it.  Returned as [(file name, contents)] pairs
    so that the driver writes them the same way it writes everything else;
    [stem] is as in {!print_program}.

    The output directory is self-contained on purpose: [dotnet build] in it
    works with nothing else installed, which is the same property that makes
    the C backend's output shippable (section 122.8). *)
val project_files : string -> program -> ML (list (string & string))

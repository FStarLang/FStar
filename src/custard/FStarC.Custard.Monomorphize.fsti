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

(** Type monomorphization (section 5.0). *)
module FStarC.Custard.Monomorphize

open FStarC.Effect
open FStarC.Custard.Syntax

(** [run prog] replaces every polymorphic type declaration by one declaration
    per instantiation appearing in [prog], renaming constructors with their
    owner's suffix.  The result has no [dt_params] and no [TVar].

    Only meaningful once rule 4 of section 3.1 has monomorphized the
    *functions* (that is, under [--custard_monomorphize_types]); a surviving
    [TVar] in a function signature has no instantiation to key on and is
    passed through untouched. *)
val run : program -> ML program

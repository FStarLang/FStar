(*
   Copyright 2008-2023 Microsoft Research

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

module FStarC.Char

(* This module is only here to be able to mention a 'char' type without
depending on FStar.Char, which brings in a lot of dependencies (see #3408).
There is no ML implementation for it. Ideally this would just be removed
after #3408.

Note that character literals will still have type 'FStar.Char.char',
and not the type defined here. *)

new
val char:eqtype

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

module FStar.Reflection.Typing.Builtins

(** This module defines some utilities in support of the reflection
    typing judgment of F*, defined in Refl.Typing.fsti.

    IT IS HIGHLY EXPERIMENTAL AND NOT YET READY TO USE.
  *)

open FStar.Reflection.V2
open FStar.Range

val dummy_range : range

val open_with (t:term) (v:term) : term
  
val open_term (t:term) (v:var) : term

val close_term (t:term) (v:var) : term

val rename (t:term) (x y:var) : term

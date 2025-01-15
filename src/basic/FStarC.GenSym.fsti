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
(*
   A simple fresh symbol generator (gensym).
*)
module FStarC.GenSym

open FStarC.Effect

(** Obtain a fresh ID. *)
val next_id             : unit -> int

(** Reset the gensym. Names generated will not be fresh with respect to
names generated before the reset. Should be used only when it is known
that freshness across resets is not needed. *)
val reset_gensym        : unit -> unit

(** Do something without affecting the gensym. Useful e.g. for printing,
to make sure there's no side effect. *)
val with_frozen_gensym  : (unit -> 'a) -> 'a

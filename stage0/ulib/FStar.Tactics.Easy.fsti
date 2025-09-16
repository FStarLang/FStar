(*
   Copyright 2008-2025 Microsoft Research

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
module FStar.Tactics.Easy

open FStar.Tactics.Effect
open FStar.Tactics.Logic.Lemmas {} (* needed to bring in lemma_from_squash into tc scope for clients *)

[@@plugin]
val easy_fill () : Tac unit

(* Call this function to solve any "easy" goals, where we just
have to introduce a bunch of binders and call SMT. *)

let easy (#a:Type) (#[easy_fill ()] x : a) : a = x

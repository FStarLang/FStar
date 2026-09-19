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
open FStar.Tactics.V2.Bare
open FStar.Tactics.Logic.Lemmas { lemma_from_squash }

let easy_fill () : Tac unit =
    (* [Lemma b] is now [Tot (squash b)], so [intro] goes through an
       [a -> Lemma b] goal on its own.  The [lemma_from_squash] switch that
       used to be needed here would now match any squashed goal and leave its
       [pre]/[post] uninstantiated. *)
    let _ = repeat intro in
    smt ()

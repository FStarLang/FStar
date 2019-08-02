(*
   Copyright 2008-2018 Microsoft Research

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
module Fail

// Making sure the unification engine respects failures

open FStar.Tactics

assume val p : Type
assume val q : Type
assume val r : Type

assume val f : squash p -> squash r
assume val g : squash q -> squash r

assume val vq : squash q

let tau () : Tac unit =
    let _ = trytac #unit (fun () -> apply (quote f); fail "oops wrong way") in
    apply (quote g);
    exact (quote vq)

let _ = assert r by tau ()

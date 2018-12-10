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
module Cut

open FStar.Tactics

assume val phi : Type
assume val psi : Type

assume val p1 : psi
assume val p2 : psi -> squash phi

let _ =
    assert_by_tactic phi
        (fun () ->
             let psi' = quote psi in
             let _ = tcut psi' in
             flip ();
             exact (`p1); // TODO: kinda pointless example
             apply (`p2);
             exact (`p1))

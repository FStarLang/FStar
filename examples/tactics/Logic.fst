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
module Logic

open FStar.Tactics.V2

let tau () : Tac unit =
    let h = implies_intro () in
    right ();
    let (h1, _) = destruct_and (binding_to_term h) in
    apply (`FStar.Squash.return_squash);
    exact (binding_to_term h1);
    qed ()

let test phi psi xi =
   assert (phi /\ xi ==> psi \/ phi) by tau ()

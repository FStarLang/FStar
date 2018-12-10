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
module Bug380_2
let single_inhabitant t = 
  forall (x y: t). x == y

let single_inhabitant_and p q
    : Lemma (single_inhabitant (p /\ q)) = ()

let single_inhabitant_bool ()
    : Lemma (single_inhabitant bool) =
  let should_fail = assert (bool == (True /\ bool)) in // Woops.  The normalizer used to simplifies `True /\ bool` into bool instead of `squash bool`
  single_inhabitant_and True bool

let falso () : Lemma False =
  single_inhabitant_bool ();
  assert (true == false)

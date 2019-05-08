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
module LeftToRight

open FStar.Tactics

assume val a : int
assume val b : int
assume val c : int

assume val lem1 : unit -> Lemma (a + a == b)
assume val lem2 : unit -> Lemma (b + a == c)
assume val lem3 : unit -> Lemma (a + b == c)

let tau () : Tac unit =
    l_to_r [`lem1; `lem2; `lem3]

let _ = assert ((a + a) + a == c) by (tau (); trefl ())
let _ = assert ((a + a) == b) by (tau (); trefl ())
let _ = assert ((b + a) == c) by (tau (); trefl ())
let _ = assert ((a + b) == c) by (tau (); trefl ())
let _ = assert ((a + b) == c) by (tau (); trefl ())

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
module Loop

(* Making sure typeclass resolution does not loop *)

open FStar.Tactics.Typeclasses

(* two classes for inhabitation *)
class c a = { x : a }
class d a = { y : a }

instance cd (dict : c 'a) : d 'a = { y = dict.x }
instance dc (dict : d 'a) : c 'a = { x = dict.y }

(* This should fail very quickly by detecting we are in a loop *)
[@expect_failure]
let f (a:Type) : a = x

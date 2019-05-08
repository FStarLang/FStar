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
module Loop2

open FStar.Tactics.Typeclasses

(* two classes for inhabitation, with an integer index *)
class c (n:nat) a = { x : a }
class d (n:nat) a = { y : a }

instance cd  (#n:nat) (_ : c n 'a) : d (n + 1) 'a = { y = x }

instance dc  (#n:nat) (_ : d n 'a) : c (n + 1) 'a = { x = y }
instance dc' (#n:nat) (_ : d n 'a) : c (n + 1) 'a = { x = y }

(* This should fail... in finite time *)
[@expect_failure]
let f (a:Type) : a = x

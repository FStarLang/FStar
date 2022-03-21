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
module FStar.Relational.State
open FStar.Relational.Relational
open FStar.Relational.Comp
open FStar.Heap
open FStar.Ref

(* Some convenient stateful functions *)
let read_rel1 r = compose2_self read (twice r)
let read_rel2 = compose2_self read
let assign_rel1 r v = compose2_self #_ #_ #_ (fun (a,b) -> write a b) (pair_rel (twice r) v)
let assign_rel2 r v = compose2_self #_ #_ #_ (fun (a,b) -> write a b) (pair_rel r v)

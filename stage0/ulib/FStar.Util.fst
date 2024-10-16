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
module FStar.Util

open FStar.Heap
open FStar.HyperStack

(* 2016-11-22: the following MUST be defined here AFTER the above `open',
   since they are used in [op_At_Plus_At] below *)
let op_Plus_Plus x y = TSet.union x y
let op_Plus_Plus_Hat x y = x ++ (TSet.singleton y)
let op_Hat_Plus_Hat  x y = (TSet.singleton x) ++ (TSet.singleton y)

let op_At_Plus_At (#a:Type) (#b:Type) (x:reference a) (y:reference b) =
   Set.union (Set.singleton (as_addr x)) (Set.singleton (as_addr y))
let op_Plus_Plus_At (#a:Type) (x:Set.set nat) (y:reference a) = Set.union x (Set.singleton (as_addr y))

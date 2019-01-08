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
module Bug101

type any (zz:Type) = fun (x:zz) -> True
assume type t (bb:Type) (p:(bb -> Type)) : Type

type node (gg:Type) = 
  | Node : v:t (node gg) (any (node gg)) -> node gg

val nodev : a:Type -> node a ->  t (node a) (any (node a))
let nodev (n:node 'a) = match n with 
  | Node v -> v

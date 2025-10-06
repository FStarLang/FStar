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
module Bug1065c

assume val t : Type

assume val proof : squash (t u#a)

#set-options "--no_smt"

val ref : _:unit{t u#a}
let ref  = proof u#a

let id1 (x : (_:unit{t u#a})) : squash (t u#a) = x

let id2 (x : squash (t u#a)) : (_:unit{t u#a}) = x

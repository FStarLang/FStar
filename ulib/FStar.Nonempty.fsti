(*
   Copyright 2026 Microsoft Research

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
module FStar.Nonempty

val nonempty (a: Type) : prop

val nonempty_intro #a (x: a) : nonempty a

// The axiom of choice.
val nonempty_elim (a: Type { nonempty a }) : GTot a

let nonempty_elim' #a (h: nonempty a) : GTot a = nonempty_elim a
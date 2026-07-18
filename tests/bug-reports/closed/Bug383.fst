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
module Bug383

type t (n:nat) = unit

(* Works *)
type v (n:nat) =
| C : t n -> v n

type u1 n = t n

(* Works *)
type v1 (n:nat) =
| C1 : u1 n -> v1 n

type u2 = t

(* Error: with --debug Extreme
datacon M.C2 : (_0:(u2 n) -> Tot (v2 n))

Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Failure("Substitution must be fully applied")
*)
type v2 (n:nat) =
| C2 : u2 n -> v2 n



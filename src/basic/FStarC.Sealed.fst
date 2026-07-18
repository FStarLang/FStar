(*
   Copyright 2008-2024 Nikhil Swamy and Microsoft Research

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
module FStarC.Sealed

(* This is the compiler-space version of the Sealed module in ulib.
Here, we define it as just an identity, but we do not expose that in
the interface so we must use the seal/unseal operations. This allows us
to

  1) make sure we do not make mistakes forgetting to seal/unseal
  2) make sure none of these operations have any runtime behavior.

It would be nicer to just make this a box type and expose that (internally
to the compiler) but that means extracted code would use the box. *)

type sealed (a:Type u#a) : Type u#a = a

let seal (x: 'a) : sealed 'a = x

let unseal (x: sealed 'a) : 'a = x

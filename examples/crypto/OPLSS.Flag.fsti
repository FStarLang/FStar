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
module OPLSS.Flag

(* An idealization flag is an abstract boolean used to toggle the use
   of a cryptographic hypothesis.

   The abstraction can be revealed in two ways:
     - In ghost code, using `reveal`
     - In concrete code, using `idealizing`

   Any use of `idealizing` must be treated as an `assume`
*)

/// abstract flag
val flag : Type u#0

/// defining a flag
val mk : bool -> flag

/// Safely revealing a flag in ghost code
val reveal : flag -> GTot bool

/// Switching between concrete and ideal in real code
val idealizing : f:flag -> b:bool{ b == reveal f }

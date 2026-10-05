(*
   Copyright 2008-2025 Microsoft Research

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
module FStarC.SmallInt

(* Native machine integers: OCaml's [int] (63 bits on 64-bit platforms).
   Arithmetic wraps around on overflow.  Meant for performance-critical
   code such as the lexer, where [int] (arbitrary-precision Zarith
   integers) is a lot slower. *)

[@@custard_extern "FStarC_SmallInt.t"]
type t : eqtype

(* Fails if the argument does not fit *)
val of_int : int -> t
val to_int : t -> int

(* The code of a character, e.g. [of_char 'a'] *)
val of_char : FStar.Char.char -> t

val zero : t
val one : t
val minus_one : t

val ( + ) : t -> t -> t
val ( - ) : t -> t -> t
val ( < ) : t -> t -> bool
val ( <= ) : t -> t -> bool
val ( > ) : t -> t -> bool
val ( >= ) : t -> t -> bool

val max : t -> t -> t
val min : t -> t -> t

val show : t -> string

val array_length (#a:Type) (arr:FStar.ImmutableArray.Base.t a) : t

(* No bounds check: the index must be in range *)
val array_index (#a:Type) (arr:FStar.ImmutableArray.Base.t a) (i:t) : a

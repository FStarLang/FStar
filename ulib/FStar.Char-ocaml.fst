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
module FStar.Char

(* The OCaml implementation: a character is its code point, an OCaml [int].
   The definitions marked [custard_extern] are not compiled, their uses refer
   to the OCaml symbol directly. *)

[@@custard_extern "int"]
private assume new type ocaml_char : eqtype

type char = ocaml_char

[@@custard_extern "FStar_UInt32.of_native_int"]
let u32_of_char _ = admit ()

[@@custard_extern "FStar_UInt32.to_native_int"]
let char_of_u32 _ = admit ()

let char_of_u32_of_char _ = admit ()

let u32_of_char_of_u32 _ = admit ()

[@@custard_extern "(fun x -> try Char.code (Char.lowercase_ascii (Char.chr x)) with _ -> x)"]
let lowercase _ = admit ()

[@@custard_extern "(fun x -> try Char.code (Char.uppercase_ascii (Char.chr x)) with _ -> x)"]
let uppercase _ = admit ()

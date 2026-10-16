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

(* OCaml implementation: [t] is OCaml's [int].  Every use of [t] prints as
   [int], so that OCaml specializes comparisons and equality on it. *)

[@@custard_extern "int"]
private assume new type ocaml_int : eqtype

type t = ocaml_int

[@@custard_extern "Obj.t"]
private assume new type obj : Type0

[@@custard_extern "Obj.repr"]
private assume val obj_repr (#a:Type) (x:a) : obj

[@@custard_extern "Obj.is_int"]
private assume val obj_is_int (o:obj) : bool

[@@custard_extern "Obj.magic"]
private assume val obj_magic (#a #b:Type) (x:a) : b

[@@custard_extern "Z.to_int"]
private assume val z_to_int (x:int) : t

(* Small Zarith integers are immediate, and then they are their own value:
   skip the C call for them. *)
let of_int x = if obj_is_int (obj_repr x) then obj_magic x else z_to_int x

[@@custard_extern "Z.of_int"]
let to_int _ = admit ()

(* [FStar.Char.char] is an OCaml [int] (a code point) too. *)
let of_char c = obj_magic c

[@@custard_extern "0"]
let zero = admit ()

[@@custard_extern "1"]
let one = admit ()

[@@custard_extern "(-1)"]
let minus_one = admit ()

[@@custard_extern "(+)"]
let ( + ) _ _ = admit ()

[@@custard_extern "(-)"]
let ( - ) _ _ = admit ()

[@@custard_extern "(<)"]
let ( < ) _ _ = admit ()

[@@custard_extern "(<=)"]
let ( <= ) _ _ = admit ()

[@@custard_extern "(>)"]
let ( > ) _ _ = admit ()

[@@custard_extern "(>=)"]
let ( >= ) _ _ = admit ()

let max a b = if a >= b then a else b

let min a b = if a <= b then a else b

[@@custard_extern "string_of_int"]
let show _ = admit ()

[@@custard_extern "Array.length"]
let array_length _ = admit ()

[@@custard_extern "Array.unsafe_get"]
let array_index _ _ = admit ()

[@@custard_extern "Z.compare"]
let int_compare _ _ = admit ()

[@@custard_extern "String.compare"]
let string_compare _ _ = admit ()

(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: N. Swamy
*)
module FStar.ImmutableArray.Base

(* The OCaml implementation: an OCaml array, never updated in place.  The
   definitions marked [custard_extern] are not compiled, their uses refer to
   the OCaml symbol directly. *)

[@@custard_extern "array"]
private assume new type ocaml_array ([@@@strictly_positive] a:Type u#a) : Type u#a

type t a = ocaml_array a

let array_has_eq _ = admit ()

[@@custard_extern "Array.of_list"]
let of_list _ = admit ()

[@@custard_extern "(fun a -> Z.of_int (Array.length a))"]
let length _ = admit ()

[@@custard_extern "(fun a i -> Array.get a (Z.to_int i))"]
let index _ _ = admit ()

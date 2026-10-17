(*
   Copyright 2008-2020 Microsoft Research

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
module FStar.Parse

(* The OCaml implementation.  The definitions marked [custard_extern] are not
   compiled, their uses refer to the OCaml symbol directly. *)

(** A primitive parser for booleans *)
[@@custard_extern "(function \"true\" -> Some true | \"false\" -> Some false | _ -> None)"]
let bool_of_string _ = admit ()

(** A primitive parser for [int] *)
[@@custard_extern "(fun s -> if String.length s = 0 then None else try Some (Z.of_string s) with Invalid_argument _ -> None)"]
let int_of_string _ = admit ()

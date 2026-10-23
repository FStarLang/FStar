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
module FStar.ImmutableArray

(* The OCaml implementation: an OCaml array, copied on every update.  The
   definitions marked [custard_extern] are not compiled, their uses refer to
   the OCaml symbol directly. *)

[@@custard_extern "Array.to_list"]
let to_list _ = admit ()

let to_list_of_list _ = admit ()

let of_list_to_list _ = admit ()

let length_spec _ = admit ()

let index_spec _ _ = admit ()

let to_list_precedes _ = admit ()

[@@custard_extern "(fun x i v -> let y = Array.copy x in y.(Z.to_int i) <- v; y)"]
let upd _ _ _ = admit ()

let length_upd _ _ _ = admit ()

let index_upd _ _ _ _ = admit ()

[@@custard_extern "(fun x v -> Array.append x [| v |])"]
let push _ _ = admit ()

let to_list_push _ _ = admit ()

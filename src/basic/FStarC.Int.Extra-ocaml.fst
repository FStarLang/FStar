(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Int.Extra

open FStarC.Effect

[@@custard_extern "Z.logand"]
let logand _ _ = admit ()

[@@custard_extern "Z.logor"]
let logor _ _ = admit ()

[@@custard_extern "Z.logxor"]
let logxor _ _ = admit ()

[@@custard_extern "Z.lognot"]
let lognot _ = admit ()

(* Zarith expects an OCaml int for the shift amount. *)
[@@custard_extern "(fun x y -> Z.shift_left x (Z.to_int y))"]
let shift_left _ _ = admit ()

[@@custard_extern "(fun x y -> Z.shift_right x (Z.to_int y))"]
let shift_right _ _ = admit ()

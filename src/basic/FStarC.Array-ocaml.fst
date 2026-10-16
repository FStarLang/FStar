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
module FStarC.Array

[@@custard_extern "array"]
private assume new type ocaml_array : Type -> Type0

type array (a:Type) = ocaml_array a

[@@custard_extern "Array.make"]
let make _ _ = admit ()

[@@custard_extern "Array.length"]
let length _ = admit ()

[@@custard_extern "Array.get"]
let get _ _ = admit ()

[@@custard_extern "Array.set"]
let set _ _ _ = admit ()

[@@custard_extern "Array.append"]
let append _ _ = admit ()

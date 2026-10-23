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
module FStarC.BaseTypes

[@@custard_extern "float"]
private assume new type ocaml_float : Type0

type float = ocaml_float
type double = ocaml_float

[@@custard_extern "(fun (x:float) -> x)"]
let float64_of_float _ = admit ()

[@@custard_extern "(fun (x:float) -> x)"]
let float_of_float64 _ = admit ()

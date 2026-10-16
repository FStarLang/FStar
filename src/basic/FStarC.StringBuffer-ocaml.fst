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
module FStarC.StringBuffer

open FStarC.Effect

[@@custard_extern "Buffer.t"]
private assume new type buffer : Type0

type t = buffer

[@@custard_extern "(fun i -> Buffer.create (Z.to_int i))"]
let create _ = admit ()

[@@custard_extern "(fun s t -> Buffer.add_string t s; t)"]
let add _ _ = admit ()

[@@custard_extern "Buffer.contents"]
let contents _ = admit ()

[@@custard_extern "(fun t -> Buffer.clear t; t)"]
let clear _ = admit ()

[@@custard_extern "Buffer.output_buffer"]
let output_channel _ _ = admit ()

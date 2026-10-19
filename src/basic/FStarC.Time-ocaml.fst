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
module FStarC.Time

open FStarC.Effect

[@@custard_extern "float"]
private assume new type ocaml_float : Type0

type time_of_day = ocaml_float

[@@custard_extern "BatUnix.gettimeofday"]
let get_time_of_day _ = admit ()

[@@custard_extern "(fun () -> Z.of_int (int_of_float (BatUnix.gettimeofday () *. 1000.0)))"]
let get_time_of_day_ms _ = admit ()

[@@custard_extern "(fun (t1:float) t2 -> t1 < t2)"]
let is_before _ _ = admit ()

[@@custard_extern "(fun f -> (BatUnix.stat f).BatUnix.st_mtime)"]
let get_file_last_modification_time _ = admit ()

[@@custard_extern "string_of_float"]
let string_of_time_of_day _ = admit ()

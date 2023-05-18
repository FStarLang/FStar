(*
   Copyright 2021 Microsoft Research

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

module Steel.ST.Loops.Util

open Steel.ST.Effect

/// Some loops utilities, implemented using the primitive Steel.ST.Loops
///

inline_for_extraction
val repeat_until
  (p:bool -> vprop)
  ($body:unit -> STT bool (p true) (fun b -> p b))
  : STT unit (p true) (fun _ -> p false)

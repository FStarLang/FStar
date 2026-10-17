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
module FStarC.PIMap

open FStarC.Effect
module M = FStarC.AVLMap

let t value = M.t int value

let cmp : M.cmp int = FStarC.SmallInt.int_compare

let empty _ = M.empty

let add map key value = M.add cmp key value map

let find_default map key dflt =
  match M.find cmp key map with
  | Some v -> v
  | None -> dflt

let try_find map key = M.find cmp key map

let fold m f a = M.fold f m a

let remove m k = M.remove cmp k m

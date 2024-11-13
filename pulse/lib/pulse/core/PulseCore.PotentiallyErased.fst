(*
   Copyright 2024 Microsoft Research

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

module PulseCore.PotentiallyErased

irreducible let is_erased: bool = true

let erased t = if is_erased then Ghost.erased t else t
let reveal x = if is_erased then Ghost.reveal x else x
let hide x = if is_erased then Ghost.hide x else x
let bind #t #s x f = if is_erased then Ghost.hide (Ghost.reveal #s (f (Ghost.reveal x))) else f x

let rec observe_bool b kif kelse =
  if is_erased then
    observe_bool b kif kelse
  else
    if coerce_eq () b then
      kif ()
    else
      kelse ()
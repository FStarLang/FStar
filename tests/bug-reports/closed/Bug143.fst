(*
   Copyright 2008-2018 Microsoft Research

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
module Bug143


type empty = | Empty : empty -> empty


val empty_is_empty : empty -> Tot (u:unit{False})
let rec empty_is_empty = function | Empty f -> empty_is_empty f


noeq type lam = | Lam : (lam -> Dv empty) -> lam


val f : lam -> Dv empty
let f l = match l with | Lam f -> f l


val delta : lam
let delta = Lam f


(* This used to only raise a warning, allowing `empty` (which has no
   inhabitants) to be inhabited by a divergent computation, and hence
   `False` to be proven. F* now demands a proof of `nonempty empty`
   for such a top-level definition, which of course fails. See #4401. *)
#push-options "--warn_error -272" //Warning_TopLevelEffect
[@@expect_failure [19]]
let omega : empty = f delta
#pop-options
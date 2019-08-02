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


val omega : empty
let omega = f delta


val bug : unit -> Lemma (requires True) (ensures False)
let bug () = empty_is_empty omega

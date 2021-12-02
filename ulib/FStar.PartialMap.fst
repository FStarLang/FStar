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

module FStar.PartialMap

open FStar.FunctionalExtensionality

type t k v = k ^-> option v

let empty k v = on_dom k (fun _ -> None)
let sel x m = m x
let upd x y m = on_dom _ (fun x1 -> if x1 = x then Some y else m x1)
let remove x m = on_dom _ (fun x1 -> if x1 = x then None else m x1)

let sel_upd _ _ _ = ()
let sel_upd_distinct_key _ _ _ _ = ()
let sel_remove _ _ = ()
let sel_remove_distinct_key _ _ _ = ()
let sel_empty _ _ = ()

let equal m1 m2 = feq m1 m2 /\ True
let eq_intro _ _ = ()
let eq_elim _ _ = ()

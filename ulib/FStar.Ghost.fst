(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.Ghost

[@@erasable]
noeq
type erased (a:Type) =
  | E of a

let reveal #a (E x) = x
let hide #a x = E x
let hide_reveal #a x = ()
let reveal_hide #a x = ()

let pull #a #b f = admit()

// let wfr_erased (a:Type)
//   : GTot (wfr_t (erased a))
//   = inverse_image_to_wfr #(erased a) #a (fun x y -> default_relation (reveal x) (reveal y)) (pull (reveal #a)) (default_wfr a)

// let erased_precedes (a:Type) (x:erased a) (y:erased a)
//   : Lemma 
//     (requires reveal x << reveal y)
//     (ensures (wfr_erased a).decreaser x << (wfr_erased a).decreaser y)
//   = ()

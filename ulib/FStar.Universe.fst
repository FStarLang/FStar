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
module FStar.Universe

(** This module implements some basic facilities to raise the universe of a type *
  * The type [raise_t a] is supposed to be isomorphic to [a] but in a higher     *
  * universe. The two functions [raise_val] and [downgrade_val] allow to coerce   *
  * from [a] to [raise_t a] and back.                                            **)

noeq type raise0 (a : Type u#a) : Type u#(max a b) =
| Ret : a -> raise0 a

let raise_t a = raise0 a
let raise_val #a x = Ret x
let downgrade_val #a x = match x with Ret x0 -> x0

let downgrade_val_raise_val #a x = ()

let raise_val_downgrade_val #a x = ()

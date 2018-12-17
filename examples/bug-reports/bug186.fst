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
module Bug186

noeq type valid : int -> Type =
  | VForall     : p:(int -> Tot int) ->
                  f: valid (p 67) ->
                  valid 42

val hoare_consequence : valid 42 -> Tot unit
let hoare_consequence v =
  let VForall p v' = v in
(*  ignore (fpp' 75) -- this causes bogus "patterns are incomplete" *)
  assert (VForall? (* this solves it: #(p 67) *) v')
    (* BUG: this makes F* explode: Impossible: Typ_unknown *)

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
module Bug707

let stexn a =
  int -> M (option a * int)

val return : (a:Type) -> (x:a) -> Tot (stexn a)
let return a x = fun s -> Some x, s

val bind : (a:Type) -> (b:Type) ->
           (f:stexn a) -> (g:a -> Tot (stexn b)) -> Tot (stexn b)
let bind a b f g =
  fun s0 ->
    let tmp = f s0 in
    match tmp with
    | None, s1_fail -> None, s1_fail
    | Some r, s1_proceed -> g r s1_proceed

let get (_:unit) : stexn int =
        fun s0 -> (Some s0, s0)

let put (s:int) : stexn unit =
        fun _ -> (Some (), s)

(* Using `stexn unit`, or any other concrete type, works *)
let raise (a:Type) : stexn a =
        fun s -> (None, s)

reifiable reflectable new_effect {
  STEXN: a:Type -> Effect
  with repr    = stexn
     ; return  = return
     ; bind    = bind
     ; get     = get
     ; put     = put
     ; raise   = raise
}

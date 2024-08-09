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
module Bug706

(* Define an effect via DM4F *)
let exnst h a = h -> M (option (a & h))

val return : (h:Type) -> (a:Type) -> (x:a) -> Tot (exnst h a)
let return h a x = fun s -> Some (x, s)

val bind : (h:Type) -> (a:Type) -> (b:Type) ->
           (f:exnst h a) -> (g:a -> Tot (exnst h b)) -> Tot (exnst h b)
let bind h a b f g =
  fun s0 ->
    let res = f s0 in
    match res with
    | None -> None
    | Some (ret, s1) -> g ret s1

reifiable reflectable new_effect {
  EXNST (h:Type): a:Type -> Effect with
    repr    = exnst h;
    bind    = bind h;
    return  = return h
}

(* This fails *)
new_effect EXNST_int = EXNST int

(* This works *)
// reifiable reflectable new_effect {
//   EXNST_int : a:Type -> Effect with
//     repr    = exnst int;
//     bind    = bind int;
//     return  = return int 
// }

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
module Bug812

let ex (a:Type) = unit -> M (option a)

val return_ex : (a:Type) -> (x:a) -> Tot (ex a)
let return_ex a x = fun _ -> Some x

val bind_ex : (a:Type) -> (b:Type) -> (f:ex a) -> (g:a -> Tot (ex b)) -> Tot (ex b)
let bind_ex a b f g = fun _ ->
  let r = f () in
  match r with
  | None -> None
  | Some x -> g x ()

let raise_ex (a:Type) (e:exn) : Tot (ex a) = fun _ -> None

reifiable reflectable new_effect {
  XEXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
     ; raise   = raise_ex
}

type arg =
| Bool | Int

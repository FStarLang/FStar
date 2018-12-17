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
module Bug1536

let ex (a:Type) = unit -> M (either a exn)

val return_ex : (a:Type) -> (x:a) -> ex a
let return_ex a x = fun _ -> Inl x

val bind_ex : (a:Type) -> (b:Type) -> (f:ex a) -> (g:a -> ex b) -> ex b
let bind_ex a b f g = fun _ ->
  let r = f () in
  match r with
  | Inr e -> Inr e
  | Inl x -> g x ()

let raise0 (a:Type) (e:exn) : ex a = fun _ -> Inr e

reifiable reflectable new_effect {
  EXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
     ; raise (#a:Type) = raise0 a
}


let ret (#a:Type0) (x:a) : EXN a (fun () p -> p (Inl x)) = x

let raise : #a:Type -> e:exn -> EXN a (fun () p -> p (Inr e)) = EXN?.raise

exception EE

#set-options "--debug Bug --debug_level SMTQuery --no_smt"

let t1 () = assert (normalize_term (reify (ret 1) ()) == Inl 1)

let t2 () = assert (normalize_term (reify (raise #int EE) ()) == Inr EE)

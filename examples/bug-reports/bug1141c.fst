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
module Bug1141c

let id (a:Type) = unit -> M a

val return_id : (a:Type) -> (x:a) -> id a
let return_id a x = fun _ -> x

val bind_id : (a:Type) -> (b:Type) -> (f:id a) -> (g:a -> id b) -> id b
let bind_id a b f g = fun _ ->
  let r = f () in g r ()

// NB: no `total` keyword, so no positivity check
reifiable reflectable new_effect {
  IDN : (a:Type) -> Effect
  with repr     = id
     ; bind     = bind_id
     ; return   = return_id
}

effect ID (a:Type) = IDN a (fun () p -> forall x. p x)

noeq
type np (a : Type) =
    | Mk : (np a -> ID a) -> np a

val self : (#a:Type) -> np a -> ID a
let self #a v =
    match v with
    | Mk f -> f v

val loop : (#a:Type) -> (a -> a) -> a

[@(expect_failure [34])]
let loop #a f = reify (self (Mk (fun x -> f (self x)))) ()

(*
val falso : unit -> squash False
let falso () = loop (fun x -> x)
*)

(* Works in Div *)
val loop_dv : (#a:Type) -> (a -> a) -> Dv a
let loop_dv #a f = reify (self (Mk (fun x -> f (self x)))) ()

val falso_dv : unit -> Dv (squash False)
let falso_dv () = loop_dv (fun x -> x)

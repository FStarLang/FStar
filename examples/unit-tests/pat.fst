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

module Patterns

type t =
  | A : int -> t
  | B : int -> t

let test_disj t = match t with
  | A i
  | B i -> i

let test (a,b)  =
  let _ = true, b in
  Cons 0 a

let rec f x = f x + 1

type T =
  | MkT of int * int
let test_impure x = MkT (f x, 0)


assume val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let test2 env el =
  fold_left (fun (out, env) wopt ->
             let w, env = None, env in
             (Cons w out), env) ([], env) el
            

let test3 map_exp env el =
  fold_left (fun (out, env) (b,wopt,e) ->
    let w, env = match wopt with
      | None -> None, env
      | Some w ->
        let w, env = map_exp env b w in
        Some w, env in
    let e, env = map_exp env b e in
    (w,e)::out, env) ([], env) el


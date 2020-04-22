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
module Bug1390

open FStar.Tactics

let taketot (f : unit -> Tot unit) : unit = ()
let takegtot (f : unit -> GTot unit) : unit = ()
let taketac (f : unit -> Tac unit) : unit = ()

let id () : Tot unit = ()

let _ = taketot id
let _ = takegtot id

[@(expect_failure [189])]
let _ = taketac id

let f0 : int -> Tot int = fun x -> x
let g0 : #a:Type -> #b:Type -> (a -> Tac b) -> a -> Tac b = fun #a #b f x -> f x

[@(expect_failure [189])]
let tau () = let x = g0 f0 2 in ()

// would get stuck
//let _ = assert True by tau ()

let f (x : int) : Tot int = x + 1

[@(expect_failure [189])]
let _ = assert_by_tactic True
            (fun () -> let l = map f [1] in
                       ())

let _ = assert_by_tactic True
            (fun () -> let l = map (fun x -> f x) [1] in
                       ())

let ff (x : int) : Tac int = x + 1

let _ = assert_by_tactic True
            (fun () -> let l = map ff [1] in
                       ())

let _ = assert_by_tactic True
            (fun () -> let l = map (fun x -> ff x) [1] in
                       ())

let rec list_sum (l:list nat) : nat =
  match l with
  | [] -> 0
  | n :: l' ->
    n + (list_sum l')

[@(expect_failure [189])]
let recursive_norm () : Tac unit =
  let ctrl (t : term) = (true, 0) in
  topdown_rewrite ctrl trefl

let recursive_norm () : Tac unit =
  let ctrl (t : term) : Tac _ = (true, 0) in
  topdown_rewrite ctrl trefl

let list_sum_lem () : Lemma (list_sum [1;2;3;4;5] = 15) =
  assert(list_sum [1;2;3;4;5] = 15)
    by (recursive_norm ())

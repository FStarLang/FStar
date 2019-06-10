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
module Clear

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

let l1 (x : bool) (y : int) (z : unit) =
    assert (phi ==> (psi ==> xi))
        by (let _ = implies_intro () in
            clear_top ();
            let _ = implies_intro () in
            clear_top ();
            exact (quote p))

let clear_all_of_type (t : typ) : Tac unit =
    let e = cur_env () in
    let bs = binders_of_env e in
    let _ = map (fun b -> if term_eq (type_of_binder b) t
                          then clear b
                          else ())
         // We need to traverse the list backwards, to clear rightmost
         // binders first. Otherwise, if we go left-first, we will revert/intro
         // over a binder we want to clear and cause it to be refreshed.
         (List.rev bs) in
    ()

let l2 (x : int) (y : bool) (z : int) =
    assert (phi ==> (psi ==> xi))
        by (let e = cur_env () in
            let n = List.length (binders_of_env e) in
            let u = quote int in
            clear_all_of_type u;
            let e = cur_env () in
            // We're removing two binders
            guard (List.length (binders_of_env e) = n - 2))

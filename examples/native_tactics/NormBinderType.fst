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
module NormBinderType

open FStar.Tactics

assume val p : int
assume val q : int

let f : int -> int = fun x -> x + 2

let g =
    synth_by_tactic #((f 3 == f 5) -> q == p)
            (fun () ->
                let b = intro () in
                admit ();

                norm_binder_type [delta; primops] b;

                match binders_of_env (cur_env ()) with
                | [b] ->
                    let t = type_of_binder b in
                    let q = quote (eq2 #int 5 7) in
                    if FStar.Order.ne (compare_term t q)
                    then fail "type was not normalized"
                    else ()
                | _ ->
                    fail "should be impossible")

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
module Retype

// Changing the type of a binder

open FStar.Tactics

assume val p : prop
assume val q : prop
assume val r : prop

assume val l : unit -> Lemma (p == r)
assume val l2 : unit -> Lemma (requires r) (ensures q)

let assumption' () : Tac unit =
    apply_raw (`FStar.Squash.return_squash);
    assumption ()

let tau () : Tac unit =
    let _ = implies_intro () in
    let _ = implies_intro () in
    let _ = implies_intro () in
    let b = implies_intro () in

    binder_retype b; // call retype, get a goal `p == ?u`
    let pp = quote p in
    let rr = quote r in
    grewrite pp rr; // rewrite p to q, get `q == ?u`
    trefl (); // unify

    apply_lemma (quote l); //prove (p == q), asked by grewrite

    let e = cur_env () in
    match binders_of_env e with
    | [_;_;_;b] ->
        let t = type_of_binder b in
        let t = norm_term [] t in // contains uvar redexes.
        if FStar.Order.ne (compare_term t rr)
        then fail "binder was not retyped?"
        else ();

        apply_lemma (quote l2);
        assumption' ();
        qed ()
    | _ ->
        fail "should be impossible"

let _ = 
    assert (True ==> True ==> True ==> p ==> q) by tau ()

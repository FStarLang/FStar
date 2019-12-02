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
module Rename

(* Testing the new printing based on the static environment *)

open FStar.Tactics

assume val phi : Type
assume val psi : Type
assume val xi : Type

assume val p : squash xi

let dump s =
    (* dump s; *)
    ()

let l1 : int -> int =
    _ by (
        dump "A";
        let x = intro () in
        dump "B";
        exact (`3))

let l2 (x : bool) (y : int) (z : unit) =
    assert (phi ==> (psi ==> xi))
        by (let h0 = implies_intro () in
            let h1 = implies_intro () in
            dump "Test";
            exact (quote p))

// this error should show pretty binders too
[@expect_failure]
let _ =
    assert (False ==> True)
        by (let h0 = implies_intro () in
            let x = quote (fun x -> 1 + x) in
            let t = mk_e_app x [pack (Tv_Const C_Unit)] in
            let _ = tc (cur_env ()) t in
            trivial ())

let constr (a b : prop) : Lemma (a ==> b ==> b /\ a) =
  assert (a ==> b ==> b /\ a)
      by (let ha = implies_intro () in
          let hb = implies_intro () in
          split ();
          mapply hb;
          mapply ha;
          qed ())

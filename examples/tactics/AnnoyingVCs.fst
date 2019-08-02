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
module AnnoyingVCs
open FStar.Tactics

assume val p : nat -> Type

let dump s =
    (* dump s; *)
    ()

assume val f : n:nat{n > 20} -> Lemma (p n)
assume val g : n:nat -> Lemma (p n)

// This must fail, we don't know if i > 20
[@expect_failure]
let test1 (i:int) =
    assume (i >= 0);
    assert (True ==> p i)
        by (dump "1";
            let _ = implies_intro () in
            dump "2";
            apply_lemma (`f))

// This should work without a guard
let test2 (i:int) =
    assume (i >= 0);
    assert (True ==> p i)
        by (dump "1";
            let _ = implies_intro () in
            dump "2";
            apply_lemma (`g);
            dump "3";
            qed ())

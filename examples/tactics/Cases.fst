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
module Cases

(* *)

open FStar.Tactics
open FStar.Mul

assume val p : Type0
assume val q : Type0
assume val r : Type0

assume val f : unit -> Lemma (p ==> r)
assume val g : unit -> Lemma (q ==> r)

let test_cases (h : (p \/ q)) : Lemma r =
    assert r
        by (let t = quote h in
            cases_or t;
            apply_lemma (quote f);
            apply_lemma (quote g);
            qed ())

// Taking a squashed hypothesis, we can unsquash it as we're in an irrelevant context
let test_cases_unsquash (h : squash (p \/ q)) : Lemma r =
    assert r
        by (let t = quote h in
            let t = unsquash t in
            cases_or t;
            apply_lemma (quote f);
            apply_lemma (quote g);
            qed ())

(* assume val pp : Type0 *)
(* assume val qq : Type0 *)
(* assume val ff :  pp -> Lemma qq *)
(* assume val gg : ~pp -> Lemma qq *)

(* let ll () : Lemma (pp \/ ~pp) = () *)

(* let test_em () : Lemma qq = *)
(*     assert qq *)
(*         by (let empp = quote ll in *)
(*             let p_or_not_p = get_lemma empp in *)
(*             let p_or_not_p = unsquash p_or_not_p in *)
(*             let h_pp_npp = cases p_or_not_p in *)
(*             let h_pp, h_npp = h_pp_npp in *)
(*             apply_lemma (quote ff); exact (h_pp); *)
(*             apply_lemma (quote gg); exact (h_npp); *)
(*             qed ()) *)

assume val pred : bool -> Type
assume val pred_true  : squash (pred true)
assume val pred_false : squash (pred false)

let test_cases_bool (b:bool) : Lemma (pred b) =
    assert (pred b)
        by (let b = quote b in
            cases_bool b;
            exact (quote pred_true);
            exact (quote pred_false);
            qed ())

let test_cases_bool_2 (x:int) : Lemma (x + x == 2 * x) =
    assert (x + x == 2 * x)
        by (let t =  quote (x = 0) in
            cases_bool t)

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
module MApply

open FStar.Tactics

assume val p : Type0
assume val q : Type0
assume val x : squash p

assume val lem     : unit -> Lemma (requires p) (ensures q)
assume val lem_imp : unit -> Lemma (p ==> q)
assume val f_sq    : squash p -> squash q
assume val f_unsq  : squash p -> q

let _ =
    assert_by_tactic q (fun () -> mapply (quote lem_imp);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote lem);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote f_sq);
                                  mapply (quote x))

let _ =
    assert_by_tactic q (fun () -> mapply (quote f_unsq);
                                  mapply (quote x))

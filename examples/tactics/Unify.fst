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
module Unify

open FStar.Tactics

let h : int =
    synth_by_tactic (fun () ->
        let l = fresh_uvar None in // None: we don't provide a type
        let r = fresh_uvar None in
        let e = cur_env () in
        apply (`op_Addition);
        exact l;
        exact r;
        let ocho = `8 in
        let _ = unify_env e r ocho in
        let _ = unify_env e l r in
        ()
    )

let _ = assert (h == 16)


(* Types do not unify, so this fails *)
val x : squash False
[@ (expect_failure [228])]
let x = assert False
            by (let w = cur_witness () in
                let e = cur_env () in
                dismiss ();
                if unify_env e w (`())
                then ()
                else fail "no")

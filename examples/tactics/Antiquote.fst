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
module Antiquote

open FStar.Tactics

let _ = assert_by_tactic True
            (fun () -> let tm = (`(1 + `@(1))) in
                       let z = 16 in
                       let x = `16 in
                       let tm2 = `(1 + `@(z)) in
                       let tm3 = `(1 + `#(x)) in
                       debug ("tm = " ^ term_to_string tm);
                       debug ("tm2 = " ^ term_to_string tm2);
                       debug ("tm3 = " ^ term_to_string tm3);
                       let ty = tc tm in
                       debug ("ty = " ^ term_to_string ty);
                       let ty2 = tc tm2 in
                       debug ("ty2 = " ^ term_to_string ty2);
                       let ty3 = tc tm3 in
                       debug ("ty3 = " ^ term_to_string ty3);
                       ())

(* TODO: When --use_extracted_interfaces is given, if we do
 * ignore (tc tm), the tactics get stuck. Investigate. *)

let _ = assert_by_tactic True
            (fun () -> let y = True in
                       let tm = `(False ==> `@y) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))

let _ = assert_by_tactic True
            (fun () -> let y = bool in
                       let tm = `(int * (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `((+) (`@y) 25) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))


let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(fun z -> z + (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(if (`@y) = 22 then (`@y) - 1 else 1 - (`@y)) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))

let _ = assert_by_tactic True
            (fun () -> let y = 5 in
                       let tm = `(match (`@y) with | 4 -> 1 + (`@y) | _ -> 99) in
                       debug ("tm = " ^ term_to_string tm);
                       ignore (tc tm))

// This one can extract, basically to mk_e_app (plus, [1; t])
let f (t : term) = `(1 + (`#t))

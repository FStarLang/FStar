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
module DeltaDepth

open FStar.Tactics

#set-options "--ugly"

type t = | A of int
         | B of bool

let f () : Tac term = mk_e_app (pack (Tv_FVar (pack_fv (cur_module () @ ["A"])))) [(`1)]

let v : t = synth_by_tactic (fun () -> exact (f ()))

(* If the `A` in `f` does not have a Data_ctor qualifier, we won't be able
 * to conclude that it's not `B`, and reducing this match will get stuck. *)
let m = match v with | B _ -> 0 | A x -> x

let _ = assert True by (let t = quote m in
                        let t' = norm_term [delta;iota] t in
                        (* print ("t' = " ^ term_to_string t'); *)
                        let r = (`1) in
                        if term_eq t' r
                        then ()
                        else fail ("The match did not reduce!:" ^ term_to_string t'))

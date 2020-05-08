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
module DependentSynth
open FStar.Tactics

let myty b = if b then int else unit

let mk_if (test e_true e_false: term) : Tac term =
  let br_true = (Pat_Constant C_True, e_true) in
  let br_false = (Pat_Constant C_False, e_false) in
  let m = pack (Tv_Match test [ br_true; br_false ] ) in
  m

let t () : Tac unit =
  let b = quote bool in
  let test' = fresh_bv b in
  let test = pack (Tv_Var test') in
  let e_true = quote 3 in
  let e_false = quote () in
  let body = mk_if test e_true e_false in
  let res = pack (Tv_Abs (mk_binder test') body) in
  // should print: function true -> 3 | false -> ()
  //debug (term_to_string res);
  t_exact true true res

let f : ((b: bool) -> Tot (myty b)) = synth_by_tactic t

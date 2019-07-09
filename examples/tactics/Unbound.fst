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
module Unbound

open FStar.Tactics

let tau () : Tac unit =
    split ();
    let x = bv_of_binder (implies_intro ()) in
    squash_intro (); exact (pack (Tv_Var x));
    // `x` is unbound in this environment, we should fail
    // (if it succeeds: is the use_bv_sorts flag on? it should be off)
    squash_intro (); exact (pack (Tv_Var x))

[@(expect_failure [228])]
let _ = assert ((False ==> False) /\ False) by tau ()

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
module Imp

open FStar.Tactics

(* Testing that intro works on implicits seamlessly *)

[@plugin]
let tau () : Tac unit =
    let b = intro () in
    exact (pack (Tv_Var (bv_of_binder b)))

let f :    int -> int = synth_by_tactic tau
let g : #x:int -> int = synth_by_tactic tau

let _ = assert (f  3 == 3)
let _ = assert (g #3 == 3)

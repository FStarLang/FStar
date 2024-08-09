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
module Bug1252

open FStar.Tactics.V2

assume val p: int -> prop
assume val p1 : squash (p 1) //NS: the squash allows p1 to be an ambient assumption in Z3

type intp = x:int{p x}

let id_intp (x: intp) : intp = x

let f : intp =
  synth_by_tactic (fun () -> exact_guard (let q_id = quote id_intp in
                                          let q_one = quote 1 in
                                          pack (Tv_App q_id (q_one, Q_Explicit))))

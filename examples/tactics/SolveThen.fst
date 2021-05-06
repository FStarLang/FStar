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
module SolveThen

open FStar.Tactics

let rec fib n : Tac unit = if n < 2 then exact (`1) else (apply (`(+)); fib (n - 1); fib (n - 2))

let f3 : int = _ by (fib 3)

let f8 : int = _ by (solve_then (fun () -> fib 8) compute)


let constr (a b : prop) : squash (a ==> b ==> b /\ a)
  = _ by
       (let ha = implies_intro () in
        let hb = implies_intro () in
        split ();
        hyp hb;
        hyp ha;
        qed ())

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
module Simplifier

open FStar.Tactics
open FStar.Tactics.Simplifier

let goal_is_true () : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | True_ -> trivial ()
    | _ -> fail "not syntactically true"

let test_simplify () : Tac unit =
    simplify ();
    or_else goal_is_true (fun () -> dump ""; fail "simplify left open goals")

let _ = assert (True /\ True)
            by test_simplify ()
let _ = assert (True \/ True)
            by test_simplify ()
let _ = assert (True \/ False)
            by test_simplify ()
let _ = assert (False \/ True)
            by test_simplify ()

let _ = assert (False \/ (True /\ True))
            by test_simplify ()
let _ = assert ((True /\ False) \/ (True /\ True))
            by test_simplify ()
let _ = assert (False \/ ((True /\ False) \/ (True /\ True)))
            by test_simplify ()

let _ = assert (False ==> True)
            by test_simplify ()
let _ = assert (False ==> False)
            by test_simplify ()
let _ = assert (True ==> True)
            by test_simplify ()

let _ = assert ((False ==> False) ==> True)
            by test_simplify ()
let _ = assert (False ==> (False ==> False))
            by test_simplify ()
let _ = assert ((False ==> False) ==> (True ==> True))
            by test_simplify ()
let _ = assert ((True ==> True) ==> (False ==> False))
            by test_simplify ()

let _ = assert (~False)
            by test_simplify ()
let _ = assert (~(~True))
            by test_simplify ()

let _ = assert (forall (x:int). True)
            by test_simplify ()
let _ = assert (forall (x:int). ((True ==> True) ==> (False ==> False)))
            by test_simplify ()

let _ = assert ((exists (x:int). False) ==> False)
            by test_simplify ()
let _ = assert (~(exists (x:int). False))
            by test_simplify ()
let _ = assert (~(exists (x:int). ((True ==> True) ==> (True ==> False))))
            by test_simplify ()

let _ = assert (False <==> False)
            by test_simplify ()
let _ = assert ((False <==> False) <==> True)
            by test_simplify ()
let _ = assert (False <==> (False <==> True))
            by test_simplify ()

let _ = assert ((exists (x:int). True) <==> True)
            by test_simplify ()
let _ = assert ((forall (x:int). False) <==> False)
            by test_simplify ()

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

open FStar.TSet
open FStar.Heap
open FStar.Preorder
open FStar.ST
open FStar.Tactics
open FStar.Tactics.Simplifier

let goal_is_true () : Tac unit =
    let g = cur_goal () in
    match term_as_formula g with
    | True_ -> trivial ()
    | _ -> fail "not syntactically true"

[@@plugin]
let test_simplify () : Tac unit =
    simplify ();
    or_else goal_is_true (fun () -> dump ""; fail "simplify left open goals")

[@@plugin]
let simplify_c () : Tac unit = dump "start"; simplify (); dump "end"; admit_all()

let test (_:unit) =
  assert (forall (x:nat). True /\ x + 1 >= 0)
       by (dump "start"; simplify(); dump "end")

#push-options "--disallow_unification_guards true"
//Factor some definitions so we don't get unexpected unificatio guards due to subtyping
let nat_addr_of (#a:Type0) (#rel:preorder a) (r:mref a rel) : GTot nat = addr_of r
let modifies_singleton #a (#rel:preorder a) (r:mref a rel) h0 h1 = modifies (Set.singleton (addr_of r)) h0 h1

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies_singleton r h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
= write #a #rel r v

let test1 (r: ref int) =
  (r := 0
  )
  <: St unit by (simplify_c ())

let test2 (r: ref int) =
  (r := 0;
   r := 1;
   r := 2;
   r := 3;
   r := 4;
   r := 5;
   r := 6;
   r := 7;
   r := 8;
   r := 9;
   r := 10)
  <: St unit by simplify_c ()

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

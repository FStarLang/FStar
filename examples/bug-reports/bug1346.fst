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
module Bug1346
open FStar.Tactics

assume val p1 (x:int) : Type0

private val __cut : (a:Type) -> (b:Type) -> (a -> b) -> a -> b
private let __cut a b f x = f x

let my_cut (t:term) : Tac unit =
    let qq = `__cut in
    let tt = pack (Tv_App qq (t, Q_Explicit)) in
    apply tt

assume val aug : (unit -> Type0) -> Type0
let test (p:(unit -> Type0)) (q:(unit -> Type0))
   = assert_by_tactic
            (p == q ==>
             aug p ==>
             aug q)
             (fun () ->
               let eq = implies_intro () in
               let h = implies_intro () in
               dump "A" ;
               my_cut (type_of_binder h);
               dump "B" ;
               rewrite eq;
               norm [] ;
               dump "C" ;
               let hh = intro () in
               apply (quote FStar.Squash.return_squash) ;
               dump "D" ;
               exact (pack (Tv_Var (bv_of_binder hh))) ; //USED TO FAIL
               exact (pack (Tv_Var (bv_of_binder h))))

let t1 () : Tac unit =
  let x     = forall_intro  () in
  let px    = implies_intro () in
  let y     = forall_intro  () in
  let eq_yx = implies_intro () in
  dump "Before";
  rewrite eq_yx;
  dump "***************After rewrite";
  squash_intro ();
  dump "***************After squash" ;
  exact (pack (Tv_Var (bv_of_binder px)));
  dump "End"

let foo1 () =
    assert_by_tactic
      (
          (forall (x:int). p1 2 ==> (forall (y:int). y == 1 ==> p1 2)) // SUCCEEDS
          ) t1;
    ()

let foo2 () =
    assert_by_tactic
      (
          (forall (x:int). p1 x ==> (forall (y:int). y == 1 ==> p1 x)) // USED TO FAIL
          ) t1;
    ()

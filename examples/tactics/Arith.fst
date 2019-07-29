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
module Arith

//

open FStar.Tactics
open FStar.Tactics.Arith
open FStar.List
open FStar.Mul

let lem0 (x:int) =
    assert (op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
        by (prune ""; addns "Prims")

// Can't locally define tactics
let tau1 () : Tac unit =
    prune "";
    FStar.Tactics.split ();
    (* rev part *)
      addns "FStar.List";
      addns "Prims";
      smt ();
    (* arithmetic part *)
      addns "Prims";
      smt ()

let lem1 (x:int) =
    assert (List.rev [1;2;3;4] == [4;3;2;1] /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
        by tau1 ()

let lem2 (x:int) =
    assert (List.rev [1;2;3;4] == [4;3;2;1] /\ op_Multiply 2 (x + 3) == 6 + (op_Multiply 3 x) - x)
        by split_arith ()

let lem3 (x y z : int) (f : int -> int) =
    assume (x + f y > 2);
    assert (x + f y > 1 /\ f == f /\ List.length (List.Tot.tail [1;2;3]) == 2)
        by split_arith ()

let lem4 (x y z : int) (f : int -> int) =
    assume (forall y. f y > y);
    assert (f 5 > 1 /\ f == f /\ List.length (List.Tot.tail [1;2;3]) == 2
            /\ 1 + 2 == 3 /\ (forall x. f (f x) > x)
            /\ (forall (x y : int). x > 2 /\ y > 2 ==> op_Multiply x y > x + y))
        by split_arith ()

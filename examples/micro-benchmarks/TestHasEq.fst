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
module TestHasEq

type mlist (a:Type) =
  | MNil : mlist a
  | MCons: hd:a -> tl:nlist a -> mlist a

and nlist (a:Type) =
  | NNil : nlist a
  | NCons: hd:a -> tl:mlist a -> nlist a

let test1 _ = assert (hasEq (mlist nat) /\ hasEq (nlist nat))

//the default, optimized hasEq scheme fails for type t
//as it cannot prove that (b x) has decidable equality
//so either, one can use noeq, in which case F* will not
//allow decidable equality on t
//or, one can say unopteq in which case, F* will use an
//alternate, unoptimized hasEq scheme
//using the alternate scheme, we can, e.g., prove test2
//but cannot prove hasEq (t nat (fun x -> (y:nat{y > x} -> bool)))
unopteq type t (a:Type) (b:a -> Type) =
  | C: x:a -> y:b x -> t a b

let test2 _ = assert (hasEq (t nat (fun x -> y:nat{y > x})))

type t1 (a:Type) =
  | C1: x:a -> y:nat -> z:nat{z = y + 2} -> t1 a

let test3 = assert (hasEq (t1 bool))

let test4 = assert (hasEq (dtuple2 nat (fun x -> y:nat{y > x})))

assume type tp (t:Type0) : Type0

type t2 (t:Type0{tp t}) =
  | Bad: t2 t

(*
 * hasEq (t3 a) depends on hasEq a, so the eqtype annotation fails
 *)
[@expect_failure]
type t3 (a:Type0) :eqtype =
  | C3: x:a -> t3 a

type t4 (a:Type0) :eqtype =  //this succeeds, since independent of a, t4 hasEq
  | C4 : x:nat -> t4 a

(*
 * Reducing basic hasEq axioms in the normalizer
 *)
#push-options "--no_smt"
let test_1514 () =
  assert (hasEq int); assert (hasEq bool); assert (hasEq string); assert (hasEq unit);
  assert (hasEq (x:int{x > 2}))
#pop-options

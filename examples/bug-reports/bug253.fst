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
module Bug253

type asym (a:Type{hasEq a}) (f: (a -> a -> Tot bool)) =
    (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)   (* anti-symmetry *)

type cmp (a:Type{hasEq a}) = f:(a -> a -> Tot bool){asym a f}

(* -- this variant succeeds *)
val p_cmp: #k:Type{hasEq k} -> #v:Type -> cmp k -> Tot unit
let p_cmp (#k:Type{hasEq k}) (#v:Type) (f:cmp k) =
  let g
    = fun (p1:k*v) (p2:k*v) -> f (fst p1) (fst p2) in
  ()

(* -- this variant fails as it should: failed to prove a pre-condition *)
val p_cmp': #k:Type{hasEq k} -> #v:Type -> cmp k -> Tot unit
let p_cmp' (#k:Type{hasEq k}) (#v:Type) (f:cmp k) =
  let g:(cmp (k * v))
    = fun (p1:k*v) (p2:k*v) -> f (fst p1) (fst p2) in
  ()

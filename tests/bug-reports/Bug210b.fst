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
module Bug210b

noeq type acc (a:Type) (r:(a -> a -> Type)) (x:a) : Type =
  | AccIntro : (y:a -> r y x -> Tot (acc a r y)) -> acc a r x

val acc_inv : #aa:Type -> #r:(aa -> aa -> Type) -> x:aa -> a:(acc aa r x) ->
              Tot (e:(y:aa -> r y x -> Tot (acc aa r y)){e << a})
let acc_inv x a = match a with | AccIntro h1 -> h1

assume val axiom1_dep : #a:Type -> #b:(a->Type) -> f:(y:a -> Tot (b y)) -> x:a ->
                        Lemma (f x << f)

val axiom1 : #a:Type -> #b:Type -> f:(a -> Tot b) -> x:a ->
             Lemma (Precedes (f x) f)
let axiom1 f x = axiom1_dep f x

assume type aa : Type
assume type r : (aa -> aa -> Type)

(* Can't prove it is total without axioms: I know that [acc_inv x a << a]
   but from this I cannot deduce [acc_inv x a y h << a] *)
val fix_F : #p:(aa -> Type) ->
            (x:aa -> (y:aa -> r y x -> Tot (p y)) -> Tot (p x)) ->
            x:aa -> a:(acc aa r x) -> Tot (p x) (decreases a)
let rec fix_F f x a =
  f x (fun y h ->
         assert(acc_inv x a << a); (* should follow from refinement; F* bug *)
           (* F* can't prove this even it's in the definition of acc_inv *)
         axiom1_dep #aa #(fun y -> r y x -> Tot (acc aa r y)) (acc_inv x a) y;
         admitP (acc_inv x a y << acc_inv x a);
         axiom1 #(r y x) #(acc aa r y) (acc_inv x a y) h;
         admitP (acc_inv x a y h << acc_inv x a y);
         admitP (acc_inv x a y h << acc_inv x a);
         admitP (acc_inv x a y h << a);
         fix_F f y (acc_inv x a y h))

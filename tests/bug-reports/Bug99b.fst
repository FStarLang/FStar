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
module Bug99b

type equivalence (a:Type) (f:(a -> a -> Tot bool)) =
    (forall (x:a). (f x x = true))
  /\ (forall (x:a) (y:a). (f x y = f y x))
  /\ (forall (x:a) (y:a) (z:a). ((f x y /\ f y z) ==> f x z))

assume type t 'a

assume val occ: m:t 'a -> x:'a -> Tot nat

assume val is_equal: t 'a -> t 'a -> Tot bool

assume val lemma_is_equal: m1:t 'a -> m2:t 'a ->
  Lemma (is_equal m1 m2 <==> (forall x. occ m1 x = occ m2 x))

val reflex: a:Type -> m:t a -> Lemma (is_equal m m)
let reflex (a:Type) m = lemma_is_equal m m

val symmetric2: a:Type -> m1:t a -> m2:t a -> Lemma (is_equal m1 m2 = is_equal m2 m1)
let symmetric2 (a:Type) m1 m2 =
  lemma_is_equal m1 m2;
  lemma_is_equal m2 m1

val symmetric1: a:Type -> m1:t a -> Lemma (forall m2. (is_equal m1 m2 = is_equal m2 m1))
let symmetric1 (a:Type) m1 = qintro #(t a) #(fun m2 -> (is_equal m1 m2 = is_equal m2 m1) == true) (symmetric2 a m1)

val transitive3: a:Type -> m1:t a -> m2:t a -> m3:t a -> Lemma ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)
let transitive3 (a:Type) m1 m2 m3 =
  if is_equal m1 m2 = true  && is_equal m2 m3
  then (
    lemma_is_equal m1 m2;
    lemma_is_equal m2 m3;
    lemma_is_equal m1 m3
  )

val transitive2: a:Type -> m1:t a -> m2:t a -> Lemma (forall (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3))
let transitive2 (a:Type) m1 m2 = qintro #(t a) #(fun m3 -> (is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3) (transitive3 a m1 m2)

val transitive1: a:Type -> m1:t a -> Lemma (forall (m2:t a) (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3))
let transitive1 (a:Type) m1 = qintro #(t a) #(fun m2 -> forall (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)) (transitive2 a m1)

val lemma_is_equal_equivalence: a:Type -> unit -> Lemma (equivalence (t a) is_equal)
let lemma_is_equal_equivalence (a:Type) () =
  qintro #(t a) #(fun m -> is_equal m m == true) (reflex a);
  qintro #(t a) #(fun m1 -> forall m2. (is_equal m1 m2 = is_equal m2 m1)) (symmetric1 a);
  qintro #(t a) #(fun m1 -> forall (m2:t a) (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)) (transitive1 a)

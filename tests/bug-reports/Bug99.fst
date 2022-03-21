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
module Bug99

type equivalence (a:Type) (f:(a -> a -> Tot bool)) =
    (forall (x:a). (f x x = true))
  /\ (forall (x:a) (y:a). (f x y = f y x))
  /\ (forall (x:a) (y:a) (z:a). ((f x y /\ f y z) ==> f x z))

assume type t 'a

assume val occ: m:t 'a -> x:'a -> Tot nat

assume val is_equal: t 'a -> t 'a -> Tot bool

assume val lemma_is_equal: m1:t 'a -> m2:t 'a ->
  Lemma (is_equal m1 m2 <==> (forall x. occ m1 x = occ m2 x))

val lemma_is_equal_equivalence: a:Type -> unit -> Lemma (equivalence (t a) is_equal)
let lemma_is_equal_equivalence (a:Type) () =
  let reflex:(m:t a -> Lemma (is_equal m m)) =
    fun m ->
    lemma_is_equal m m
  in

  let symmetric1:(m1:t a -> Lemma (forall m2. (is_equal m1 m2 = is_equal m2 m1))) =
    fun m1 ->
    let symmetric2:(m2:t a -> Lemma (is_equal m1 m2 = is_equal m2 m1)) = fun m2 ->
      lemma_is_equal m1 m2;
      lemma_is_equal m2 m1
    in
    qintro #(t a) #(fun m2 -> (is_equal m1 m2 = is_equal m2 m1) == true) symmetric2
  in

  let transitive1:(m1:t a -> Lemma (forall (m2:t a) (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3))) =
    fun m1 ->
    let transitive2:(m2:t a -> Lemma (forall (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3))) =
      fun m2 ->
      let transitive3:(m3:t a -> Lemma ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)) =
        fun m3 ->
        if is_equal m1 m2 = true  && is_equal m2 m3
        then (
          lemma_is_equal m1 m2;
          lemma_is_equal m2 m3;
          lemma_is_equal m1 m3
        )
      in
      qintro #(t a) #(fun m3 -> (is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3) transitive3
    in
    qintro #(t a) #(fun m2 -> forall (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)) transitive2
  in

  qintro #(t a) #(fun m -> is_equal m m == true) reflex;
  qintro #(t a) #(fun m1 -> forall m2. (is_equal m1 m2 = is_equal m2 m1)) symmetric1;
  qintro #(t a) #(fun m1 -> forall (m2:t a) (m3:t a). ((is_equal m1 m2 /\ is_equal m2 m3) ==> is_equal m1 m3)) transitive1

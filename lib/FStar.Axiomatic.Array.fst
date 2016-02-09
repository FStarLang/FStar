(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(* A logical theory of integer-indexed arrays, from [0, n) *)
module FStar.Axiomatic.Array

type seq            : Type -> Type
assume val index    : #a:Type -> seq a -> int -> Tot a
assume val update   : #a:Type -> seq a -> int -> a -> Tot (seq a)
assume val emp      : a:Type -> Tot (seq a)
assume val create   : #a:Type -> int -> a -> Tot (seq a)

assume val length   : #a:Type -> seq a -> Tot nat
assume val slice    : #a:Type -> seq a -> int -> int -> Tot (seq a)
assume val append   : #a:Type -> seq a -> seq a -> Tot (seq a)
assume val proj_some: #a:Type -> seq (option a) -> Tot (seq a)
type Equal          : #a:Type -> seq a -> seq a -> Type
type array (a:Type) = ref (seq a)

assume LengthConst:  forall (a:Type) (n:int) (v:a).{:pattern (length (create n v))} 
                     length (create n v) == n 

assume IndexConst:   forall (a:Type) (n:int) (v:a) (i:int). {:pattern (index (create n v) i)} 
                     (0 <= i /\ i < n) 
                     ==> index (create n v) i == v

assume LengthUpdate: forall (a:Type) (s:seq a) (i:int) (v:a). {:pattern (length (update s i v))} 
                     (0 <= i /\ i < length s) 
                     ==> length (update s i v) == length s

assume IndexUpdate:  forall (a:Type) (s:seq a) (i:int) (v:a) (n:int). {:pattern (index (update s i v) n)} 
                     (0 <= n /\ n <= length s)
                     ==>  (if i==n
                           then index (update s i v) n == v 
                           else index (update s i v) n == index s n)

assume LengthSlice:  forall (a:Type) (s:seq a) (i:int) (j:int). {:pattern (length (slice s i j))} 
                     (0 <= i /\ i <= j /\ j <= length s) 
                     ==> j - i == length (slice s i j)

assume IndexSlice:   forall (a:Type) (s:seq a) (i:int) (j:int) (k:int). {:pattern (index (slice s i j) k)} 
                     (0 <= k /\ k <= length (slice s i j)) 
                     ==> index (slice s i j) k == index s (i + k)

assume LengthAppend: forall (a:Type) (s1:seq a) (s2:seq a). {:pattern (length (append s1 s2))} 
                     length (append s1 s2) == length s1 + length s2

assume IndexAppend:  forall (a:Type) (s1:seq a) (s2:seq a) (i:int). {:pattern (index (append s1 s2) i)}
                     if (0 <= i /\ i < length s1) 
                     then index (append s1 s2) i == index s1 i
                     else index (append s1 s2) i == index s2 (i - length s1)

assume SeqEquals:    forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Equal s1 s2)} 
                     Equal s1 s2
                     <==> (length s1 == length s2
                           /\ (forall (i:int).{:pattern (index s1 i); (index s2 i)} 
                               (0 <= i /\ i < length s1) 
                               ==> index s1 i == index s2 i))

assume Extensional:  forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Equal s1 s2)} 
                     Equal s1 s2
                     ==> s1 == s2

assume ProjEmp:      forall (a:Type).{:pattern (proj_some (emp (option a)))}
                     length (proj_some (emp (option a)))==0

assume ProjLen:      forall (a:Type) (s:seq (option a)).{:pattern  (proj_some s)} 
                     length (proj_some s)==length s

(* assume ProjIndex:    forall (a:Type) (s:seq (option a)) (i:int).{:pattern  (index (proj_some s) i)}  *)
(*                      (0 <= i /\ i <= length (proj_some s))  *)
(*                      ==> index (proj_some s) i == Some.v (index s i) *)

assume EmpConst:     forall (a:Type) (s:seq a).{:pattern (length s)}
                     length s == 0 
                     ==> s==emp a

type IsSomeAll (a:Type) (s:seq (option a)) = (forall (i:int). (0 <= i /\ i < length s) ==> is_Some (index s i))


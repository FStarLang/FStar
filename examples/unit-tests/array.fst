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
module Array
type seq : Type => Type
type array 'a = ref (seq 'a)
logic val Index   : seq 'a -> int -> 'a
logic val Update  : seq 'a -> int -> 'a -> seq 'a
logic val Emp     : 'a:Type -> seq 'a
logic val Const   : int -> 'a -> seq 'a
logic val Length  : seq 'a -> int
logic val Slice   : seq 'a -> int -> int -> seq 'a
logic val Append  : seq 'a -> seq 'a -> seq 'a
logic val ProjSome: seq (option 'a) -> seq 'a
type Equal : #'a:Type => seq 'a => seq 'a => Type

assume LengthConst:  forall n v.{:pattern (Length (Const n v))} Length (Const n v) == n 
assume IndexConst:   forall 'a (n:int) (v:'a) (i:int). {:pattern (Index (Const n v) i)} (0 <= i /\ i < n) ==> (Index (Const n v) i == v)
assume LengthUpdate: forall s (i:int) v. {:pattern (Length (Update s i v))} (0 <= i /\ i < Length s) ==> Length (Update s i v) == Length s
assume IndexUpdate:  forall s i v (n:int). {:pattern (Index (Update s i v) n)} (0 <= n /\ n <= Length s) 
                                      ==>  (if (i==n) then Index (Update s i v) n == v else Index (Update s i v) n==Index s n)
assume LengthSlice:  forall s (i:int) (j:int). {:pattern (Length (Slice s i j))} (0 <= i /\ i <= j /\ j <= Length s) ==> (j - i == Length (Slice s i j))
assume IndexSlice:   forall s i j (k:int). {:pattern (Index (Slice s i j) k)} (0 <= k /\ k <= Length (Slice s i j)) ==> (Index (Slice s i j) k == Index s (Add i k))
assume LengthAppend: forall s t. {:pattern (Length (Append s t))} Length (Append s t) == (Length s + Length t)
assume IndexAppend:  forall s t (i:int). {:pattern (Index (Append s t) i)} 
                                         (if (0 <= i /\ i < Length s) 
                                          then Index (Append s t) i == Index s i
                                          else Index (Append s t) i == Index t (i - Length s))
assume SeqEquals:    forall s0 s1.{:pattern (Equal s0 s1)} (Equal s0 s1)
                                                            <==> (Length s0 == Length s1
                                                                  /\ (forall (i:int).{:pattern (Index s0 i); (Index s1 i)} (0 <= i /\ i < Length s0) ==> (Index s0 i == Index s1 i)))
assume Extensional:  forall s t.{:pattern (Equal s t)} Equal s t ==> (s == t)
assume ProjSomeEmpty: forall ('a:Type) (s:seq (option 'a)). (Length s == 0) ==> (ProjSome s==Emp 'a)
assume ProjSomeLength: forall ('a:Type) (s:seq (option 'a)).{:pattern  (ProjSome s)} (Length (ProjSome s) == Length s)
assume IndexProjSome: forall ('a:Type) (s:seq (option 'a)) (i:int).{:pattern  (Index (ProjSome s) i)} (0 <= i /\ i <= Length (ProjSome s)) ==> (Index (ProjSome s) i == Some.v (Index s i))
assume EmpConst: forall ('a:Type) (s:seq 'a). (Length s == 0) ==> (s == Emp)
type IsSomeAll: _ = fun ('a:Type) (s:seq (option 'a)) => 
    (forall (i:int). (0 <= i /\ i < Length s) ==> b2t (is_Some (Index s i)))

assume val mk_array: list 'a -> array 'a
end

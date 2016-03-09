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
module Sort

type SortedRange : int => int => list int => E
assume Nil_Sorted : forall (n:int) (m:int). n <= m <==> SortedRange n m [] 
assume Cons_Sorted: forall (n:int) (m:int) (hd:int) (tl:list int). 
               SortedRange hd m tl && (n <= hd) && (hd <= m)
          <==> SortedRange n m (hd::tl)

val append: n1:int -> n2:int{n1 <= n2} -> n3:int{n2 <= n3} -> n4:int{n3 <= n4} 
         -> i:list int{SortedRange n1 n2 i} 
         -> j:list int{SortedRange n3 n4 j}
         -> k:list int{SortedRange n1 n4 k 
                      /\ (forall x. In x k <==> In x i \/ In x j)}
let rec append n1 n2 n3 n4 i j = match i with 
  | [] -> 
    (match j with
      | [] -> j
      | _::_ -> j)
  | hd::tl -> hd::(append hd n2 n3 n4 tl j)

val partition: x:int
            -> l:list int
            -> (lo:list int
                * hi:list int{(forall y. In y lo ==> y <= x /\ In y l)
                               /\ (forall y. In y hi ==> x < y /\ In y l)
                               /\ (forall y. In y l ==> In y lo \/ In y hi)})
let rec partition x l = match l with
  | [] -> ([], [])
  | hd::tl ->
    let lo, hi = partition x tl in
    if hd <= x
    then (hd::lo, hi)
    else (lo, hd::hi)

logic val Min : list int -> int
logic val Max : list int -> int
type IsMin : list int => int => E
type IsMax : list int => int => E
assume Min_IsMin: forall l. IsMin l (Min l)
assume Max_IsMax: forall l. IsMax l (Max l)
assume Min_Max: forall l i j. IsMin l i /\ IsMax l j ==> i <= j
assume Min_min: forall l i. IsMin l i <==> (forall x. In x l ==> i <= x)
assume Max_max: forall l i. IsMax l i <==> (forall x. In x l ==> x <= i)

val sort: i:list int
       -> j:list int{(forall a b. IsMin i a /\ IsMax i b ==> SortedRange a b j) /\ (forall x. In x i <==> In x j)}
let rec sort i = match i with
  | [] -> []
  | hd::tl ->
    let lo,hi = partition hd tl in
    let i' = sort lo in 
    let j' = sort hi in
    assert (IsMin i' (Min i));
    assert (IsMax i' hd);
    assert (SortedRange (Min i) hd i');
    assert (IsMin (hd::j') hd);
    assert (IsMax (hd::j') (Max i));
    assert (SortedRange hd (Max i) (hd::j'));
    append (Min i) hd hd (Max i) i' (hd::j')


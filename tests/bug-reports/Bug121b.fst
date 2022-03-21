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
module Bug121b

open FStar.List

assume val pairs_with_sum (n: nat) : list (p: (nat * nat){fst p + snd p == n})

assume val product (#a #b: Type) (l1: list a) (l2: list b) : list (a * b)

type bin_tree =
| Leaf
| Branch of bin_tree * bin_tree

let rec size bt : nat =
  match bt with
  | Leaf -> 0
  | Branch(l, r) -> 1 + size l + size r

let rec trees_of_size (s: nat) : list bin_tree =
  if s = 0 then
    [Leaf]
  else
    List.Tot.concatMap #(p: (nat * nat){(fst p) + (snd p) == s - 1})
      (fun (s1, s2) -> List.Tot.map Branch (product (trees_of_size s1) (trees_of_size s2)))
      (pairs_with_sum (s - 1))

let unfold_tos (s: nat) : Lemma (trees_of_size s ==
             (if s = 0 then
               [Leaf]
             else
               List.Tot.concatMap #(p: (nat * nat){(fst p) + (snd p) == s - 1})
                 (fun (s1, s2) -> List.Tot.map Branch (product (trees_of_size s1) (trees_of_size s2)))
                 (pairs_with_sum (s - 1)))) =
  assert_norm (trees_of_size s ==
         (if s = 0 then
           [Leaf]
         else
           List.Tot.concatMap #(p: (nat * nat){(fst p) + (snd p) == s - 1})
             (fun (s1, s2) -> List.Tot.map Branch (product (trees_of_size s1) (trees_of_size s2)))
             (pairs_with_sum (s - 1))))

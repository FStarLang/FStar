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
module NegativeTests.BST

(* The type of a binary tree indexed by its max element *)
type tree: int -> Type =
  | Leaf : n:int -> tree n
  | Node : #l   :int
        -> left :option (tree l)
        -> n    :int
        -> #r   :int
        -> right:option (tree r){l <= n
                                 /\ n <= r
                                 /\ (None? right == (n=r))
                                 /\ (None? left == (n=l))}
        -> tree r


let test_node_1 () = Node #1 None 1 #1 None
let test_node_2 (l:int) (t:tree l) = Node (Some t) (l + 1) #(l + 1) None
let test_node_3 (l:int) (t1:tree l) (t2:tree (l + 2)) = Node (Some t1) (l + 1) (Some t2)

[@@(expect_failure [19])]
let bad_node_1 () = Node #0 None 1 #2 None                                              //fails: needs to be Node #1 None 1 #1 None

[@@(expect_failure [19])]
let bad_node_2 (l:int) (t:tree l) = Node (Some t) l #(l + 1) None                       //fails: needs to be (l + 1) in the middle

[@@(expect_failure [19])]
let bad_node_3 (l:int) (t1:tree l) (t2:tree (l + 1)) = Node (Some t1) (l + 1) (Some t2) //fails: t2 must be at least tree (l + 2)

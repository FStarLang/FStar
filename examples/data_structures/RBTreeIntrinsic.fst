(*
   Copyright 2019 Microsoft Research

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
(**
 *  Okasaki Red-Black trees in F*
 * 
 *  https://www.cs.tufts.edu/~nr/cs257/archive/chris-okasaki/redblack99.pdf
 * 
 *  Compare with
 *  - https://github.com/sweirich/dth/tree/master/depending-on-types
 *  - https://lists.chalmers.se/pipermail/agda/2012/003697.html
 *  - The "extrinsic" style alternative in examples/data_structures/RBTree.fst
 * 
 *  Extract to OCaml and run with [make test] to get a REPL for playing with
 *  the code.
 *
 *  Author: Dany Fabian
 *  Minor tweaks, comments, and OCaml test driver by Santiago Zanella-Beguelin 
**)
module RBTreeIntrinsic

/// Much of the file verifies with fuel=0, max_ifuel=1
#set-options "--max_fuel 2 --max_ifuel 2 --z3rlimit 80"

type color =
| Red
| Black

let chain x y z =
  match x, z with
  | Some x, Some z -> x <= y && y <= z
  | Some x, None -> x <= y
  | None, Some z -> y <= z
  | _ -> true

/// The following is enforced by the type:
///
/// - Each node is either Red or Black
/// - All leaves are Black
/// - If a node is Red then its two children are Black
/// - Every path from a given node to any leaf has the same number of Black nodes
///   (i.e. the Black height of the tree is a constant)
///
/// This implies that the path from the root to the farthest leaf is
/// at most twice as long as the path from the root to the nearest leaf.
///
/// The type does not enforce that the root is Black, or that the tree
/// is a binary search tree.
///
/// It's easy to make it polymoprhic on the type of values, but here we fix [int]
type rbnode : h:nat -> c:color -> Type =
| Leaf :
  rbnode 1 Black
| R : #h:nat ->
  left:rbnode h Black -> value:int -> right:rbnode h Black ->
  rbnode h Red
| B : #h:nat -> #cl:color -> #cr:color ->
  left:rbnode h cl -> value:int -> right:rbnode h cr ->
  rbnode (h+1) Black

/// The default lexicographic order for proving termination would
/// require proving that the color "decreases" in recursive calls. The
/// lexicographic order on color is [Red << Black] (because of the
/// order of constructors in its definition), but this doesn't
/// decrease when the root is [Black], hence why we need to explicitly
/// say that the argument that decreases is [root].
val reduceNode : #h:nat -> #c:color
  -> f:(int -> int -> int) -> root:rbnode h c -> Tot (option int) (decreases root)
let rec reduceNode #h #c f = function
  | Leaf -> None
  | B left value right
  | R left value right ->
    match reduceNode f left, reduceNode f right with
    | Some l, Some r -> Some (f value (f l r))
    | Some x, None
    | None, Some x -> Some (f x value)
    | None, None -> Some value

val min: #h:nat -> #c:color -> t:rbnode h c -> option int
let min #h #c t = reduceNode (fun x y -> if x < y then x else y) t

val max: #h:nat -> #c:color -> t:rbnode h c -> option int
let max #h #c t = reduceNode (fun x y -> if x > y then x else y) t

val sorted : #h:nat -> #c:color -> root:rbnode h c -> Tot bool (decreases root)
let rec sorted #h #c = function
  | Leaf -> true
  | B left value right
  | R left value right ->
    sorted left && sorted right && chain (max left) value (min right)

/// The type of Red-Black trees (sorted and with a Black root)
type rbtree =
  | RBTree : #h:nat -> root:rbnode h Black {sorted root} -> rbtree

/// Non-empty subtree
type hiddenTree : h:nat -> Type =
  | HR : #h:nat -> node:rbnode h Red -> hiddenTree h
  | HB : #h:nat -> node:rbnode (h+1) Black -> hiddenTree (h+1)

type almostNode : h:nat -> Type =
  | LR : #h:nat -> #cR:color -> left:rbnode h Red -> value:int -> right:rbnode h cR -> almostNode h
  | RR : #h:nat -> #cL:color -> left:rbnode h cL -> value:int -> right:rbnode h Red -> almostNode h
  | V : #h:nat -> #c:color -> node:rbnode h c -> almostNode h

val balanceLB : #h:nat -> #c:color -> almostNode h -> int -> rbnode h c -> Tot (hiddenTree (h+1))
let balanceLB #h #c left z d =
  match left with
  | LR (R a x b) y c
  | RR a x (R b y c) -> HR (R (B a x b) y (B c z d))
  | V axb -> HB (B axb z d)

val balanceRB : #h:nat -> #c:color -> rbnode h c -> int -> almostNode h -> Tot (hiddenTree (h+1))
let balanceRB #h #c a x right =
  match right with
  | LR (R b y c) z d
  | RR b y (R c z d) -> HR (R (B a x b) y (B c z d))
  | V cyd -> HB (B a x cyd)

val balanceLR : #h:nat -> #c:color -> hiddenTree h -> int -> rbnode h c -> Tot (almostNode h)
let balanceLR #h #c left x right =
  match left with
  | HR a -> LR a x right
  | HB a ->
    match right with
    | R b y c -> RR a x (R b y c)
    | B b y c -> V (R a x (B b y c))
    | Leaf -> V (R a x Leaf)

val balanceRR : #h:nat -> #c:color -> rbnode h c -> int -> hiddenTree h -> Tot (almostNode h)
let balanceRR #h #c left y right =
  match right with
  | HR c -> RR left y c
  | HB c ->
    match left with
    | R a x b -> LR (R a x b) y c
    | B a x b -> V (R (B a x b) y c)
    | Leaf -> V (R Leaf y c)

val ins : #h:nat -> #c:color -> x:int -> s:rbnode h c -> Tot (almostNode h) (decreases s)
val insB : #h:nat -> x:int -> s:rbnode h Black -> Tot (hiddenTree h) (decreases s)
let rec ins #h #c x = function
  | Leaf -> V (R Leaf x Leaf)
  | B a y b ->
    (if x < y then
    match balanceLB (ins x a) y b with
    | HR r -> V r
    | HB b -> V b
    else if x = y then V (B a y b)
    else match balanceRB a y (ins x b) with
    | HR r -> V r
    | HB b -> V b)
  | R a y b ->
    (if x < y then balanceLR (insB x a) y b
     else if x = y then V (R a y b)
     else balanceRR a y (insB x b))
and insB #h x = function
  | Leaf -> HR (R Leaf x Leaf )
  | B a y b ->
    if x < y then balanceLB (ins x a) y b
    else if x = y then HB (B a y b)
    else balanceRB a y (ins x b)

val mem : #h:nat -> #c:color -> x:int -> s:rbnode h c -> Tot bool (decreases s)
let rec mem #h #c x = function
  | Leaf -> false
  | B l y r
  | R l y r -> x = y || mem x l || mem x r

val hiddenTree_mem : #h:nat -> int -> hiddenTree h -> bool
let hiddenTree_mem #h x = function
  | HB root
  | HR root -> mem x root

val almostNode_mem : #h:nat -> int -> almostNode h -> bool
let almostNode_mem #h x = function
  | LR a y b
  | RR a y b -> mem x (B a y b)
  | V root -> mem x root

val ins_mem : #h:nat -> #c:color -> x:int -> s:rbnode h c ->
  Lemma (ensures forall y. (mem y s \/ y = x) <==> almostNode_mem y (ins x s)) (decreases s)

val insB_mem : #h:nat -> x:int -> s:rbnode h Black ->
  Lemma (ensures forall y. (mem y s \/ y = x) <==> hiddenTree_mem y (insB x s)) (decreases s)

let rec ins_mem #h #c x = function
  | Leaf -> ()
  | B a y b ->
    if x < y then ins_mem x a
    else if x = y then ()
    else ins_mem x b
  | R a y b ->
    if x < y then insB_mem x a
    else if x = y then ()
    else insB_mem x b
and insB_mem #h x = function
  | Leaf -> ()
  | B a y b ->
    if x < y then ins_mem x a
    else if x = y then ()
    else ins_mem x b

val almostNode_sorted : #h:nat -> almostNode h -> bool
let almostNode_sorted #h = function
  | LR a x b
  | RR a x b -> sorted (B a x b)
  | V root -> sorted root

val hiddenTree_sorted : #h:nat -> hiddenTree h -> bool
let hiddenTree_sorted #h = function
  | HB root
  | HR root -> sorted root

val hiddenTree_max : #h:nat -> hiddenTree h -> option int
let hiddenTree_max #h = function
  | HB root
  | HR root -> max root

val hiddenTree_min : #h:nat -> hiddenTree h -> option int
let hiddenTree_min #h = function
  | HB root
  | HR root -> min root

val almostNode_max : #h:nat -> almostNode h -> option int
let almostNode_max #h = function
  | LR a x b
  | RR a x b
  | V (R a x b)
  | V (B a x b) -> max (B a x b)
  | V Leaf -> None

val almostNode_min : #h:nat -> almostNode h -> option int
let almostNode_min #h = function
  | LR a x b
  | RR a x b
  | V (R a x b)
  | V (B a x b) -> min (B a x b)
  | V Leaf -> None

let atLeast x = function
  | Some y -> x <= y
  | None -> true

let atMost x = function
  | Some y -> x >= y
  | None -> true

val global_upper_bound : #h:nat -> #c:color -> z:int -> s:rbnode h c ->
  Lemma 
  (requires atMost z (max s))
  (ensures  forall y. mem y s ==> y <= z)
  (decreases s)
let rec global_upper_bound #h #c z = function
  | Leaf -> ()
  | R a y b
  | B a y b ->
    global_upper_bound z a;
    global_upper_bound z b

val global_lower_bound : #h:nat -> #c:color -> z:int -> s:rbnode h c {atLeast z (min s)} ->
  Lemma 
  (requires atLeast z (max s))
  (ensures  forall y. mem y s ==> y >= z)
  (decreases s)
let rec global_lower_bound #h #c z = function
  | Leaf -> ()
  | R a y b
  | B a y b ->
    global_lower_bound z a;
    global_lower_bound z b

val mem_to_max : #h:nat -> #c:color -> z:int -> n:rbnode h c ->
  Lemma 
  (requires forall y. mem y n ==> y <= z) 
  (ensures  atMost z (max n)) 
  (decreases n)
let rec mem_to_max #h #c z = function
  | Leaf -> ()
  | R a y b
  | B a y b ->
    mem_to_max z a;
    mem_to_max z b

val mem_to_min : #h:nat -> #c:color -> z:int -> n:rbnode h c ->
  Lemma 
  (requires forall y. mem y n ==> y >= z) 
  (ensures  atLeast z (min n))
  (decreases n)
let rec mem_to_min #h #c z = function
  | Leaf -> ()
  | R a y b
  | B a y b ->
    mem_to_min z a;
    mem_to_min z b

val almostNode_mem_to_max : #h:nat -> z:int -> n:almostNode h ->
  Lemma 
  (requires forall y. almostNode_mem y n ==> y <= z) 
  (ensures  atMost z (almostNode_max n)) 
  (decreases n)
let almostNode_mem_to_max #h z = function
  | V node -> mem_to_max z node
  | LR a x b
  | RR a x b -> mem_to_max z (B a x b)

val almostNode_mem_to_min : #h:nat -> z:int -> n:almostNode h ->
  Lemma 
  (requires forall y. almostNode_mem y n ==> y >= z)
  (ensures  atLeast z (almostNode_min n)) 
  (decreases n)
let almostNode_mem_to_min #h z = function
  | V node -> mem_to_min z node
  | LR a x b
  | RR a x b -> mem_to_min z (B a x b)

val hiddenTree_mem_to_max : #h:nat -> z:int -> n:hiddenTree h ->
  Lemma 
  (requires forall y. hiddenTree_mem y n ==> y <= z)
  (ensures  atMost z (hiddenTree_max n))
  (decreases n)
let hiddenTree_mem_to_max #h z = function
  | HR node
  | HB node -> mem_to_max z node

val hiddenTree_mem_to_min : #h:nat -> z:int -> n:hiddenTree h ->
  Lemma 
  (requires forall y. hiddenTree_mem y n ==> y >= z) 
  (ensures  atLeast z (hiddenTree_min n)) 
  (decreases n)
let hiddenTree_mem_to_min #h z = function
  | HR node
  | HB node -> mem_to_min z node

val ins_max : #h:nat -> #c:color -> z:int -> x:int -> s:rbnode h c -> t:almostNode h ->
  Lemma 
  (requires x <= z /\ atMost z (max s) /\ (forall y. mem y s \/ x = y <==> almostNode_mem y t)) 
  (ensures atMost z (almostNode_max t))
let ins_max #h #c z x s t =
  global_upper_bound z s;
  almostNode_mem_to_max z t

val ins_min : #h:nat -> #c:color -> z:int -> x:int -> s:rbnode h c -> t:almostNode h ->
  Lemma 
  (requires x >= z /\ atLeast z (min s) /\ (forall y. mem y s \/ x = y <==> almostNode_mem y t)) 
  (ensures atLeast z (almostNode_min t))
let ins_min #h #c z x s t =
  global_lower_bound z s;
  almostNode_mem_to_min z t

val insB_max : #h:nat -> #c:color -> z:int -> x:int -> s:rbnode h c -> t:hiddenTree h ->
  Lemma 
  (requires x <= z /\ atMost z (max s) /\ (forall y. mem y s \/ x = y <==> hiddenTree_mem y t))
  (ensures  atMost z (hiddenTree_max t))
let insB_max #h #c z x s t =
  global_upper_bound z s;
  hiddenTree_mem_to_max z t

val insB_min : #h:nat -> #c:color -> z:int -> x:int -> s:rbnode h c  -> t:hiddenTree h ->
  Lemma 
  (requires x >= z /\ atLeast z (min s) /\ (forall y. mem y s \/ x = y <==> hiddenTree_mem y t)) 
  (ensures  atLeast z (hiddenTree_min t))
let insB_min #h #c z x s t =
  global_lower_bound z s;
  hiddenTree_mem_to_min z t

val balanceLB_preserves_sort : #h:nat -> #c:color -> a:almostNode h -> x:int -> b:rbnode h c ->
  Lemma 
  (requires almostNode_sorted a /\ sorted b /\ chain (almostNode_max a) x (min b))
  (ensures  hiddenTree_sorted (balanceLB a x b))
let balanceLB_preserves_sort #h #c left z d = ()

val balanceRB_preserves_sort : #h:nat -> #c:color -> a:rbnode h c -> x:int -> b:almostNode h ->
  Lemma 
  (requires sorted a /\ almostNode_sorted b /\ chain (max a) x (almostNode_min b))
  (ensures  hiddenTree_sorted (balanceRB a x b))
let balanceRB_preserves_sort #h #c a x right = ()

val balanceLR_preserves_sort : #h:nat -> #c:color -> a:hiddenTree h -> x:int -> b:rbnode h c ->
  Lemma 
  (requires hiddenTree_sorted a /\ sorted b /\ chain (hiddenTree_max a) x (min b))
  (ensures  almostNode_sorted (balanceLR a x b))
let balanceLR_preserves_sort #h #c a x b = ()

val balanceRR_preserves_sort : #h:nat -> #c:color -> a:rbnode h c -> x:int -> b:hiddenTree h ->
  Lemma 
  (requires sorted a /\ hiddenTree_sorted b /\ chain (max a) x (hiddenTree_min b))
  (ensures  almostNode_sorted (balanceRR a x b))
let balanceRR_preserves_sort #h #c a x b = ()

val ins_preserves_sort : #h:nat -> #c:color -> x:int -> s:rbnode h c ->
  Lemma 
  (requires sorted s) 
  (ensures  almostNode_sorted (ins x s)) 
  (decreases s)

val insB_preserves_sort : #h:nat -> x:int -> s:rbnode h Black ->
  Lemma 
  (requires sorted s) 
  (ensures  hiddenTree_sorted (insB x s)) 
  (decreases s)

let rec ins_preserves_sort #h #c x = function
  | Leaf -> ()
  | B a y b ->
    if x < y then
    begin
      ins_preserves_sort x a;
      ins_mem x a;
      ins_max y x a (ins x a);
      balanceLB_preserves_sort (ins x a) y b
    end
    else if x = y then ()
    else
    begin
      ins_preserves_sort x b;
      ins_mem x b;
      ins_min y x b (ins x b);
      balanceRB_preserves_sort a y (ins x b)
    end
  | R a y b ->
    if x < y then
    begin
      insB_preserves_sort x a;
      insB_mem x a;
      insB_max y x a (insB x a);
      balanceLR_preserves_sort (insB x a) y b
    end
    else if x = y then ()
    else
    begin
      insB_preserves_sort x b;
      insB_mem x b;
      insB_min y x b (insB x b);
      balanceRR_preserves_sort a y (insB x b)
    end
and insB_preserves_sort #h x = function
  | Leaf -> ()
  | B a y b ->
    if x < y then
    begin
      ins_preserves_sort x a;
      ins_mem x a;
      ins_max y x a (ins x a);
      balanceLB_preserves_sort (ins x a) y b
    end
    else if x = y then ()
    else
    begin
      ins_preserves_sort x b;
      ins_mem x b;
      ins_min y x b (ins x b);
      balanceRB_preserves_sort a y (ins x b)
    end

val insert : int -> rbtree -> rbtree
let insert x tree =
  ins_preserves_sort x tree.root;
  match ins x tree.root with
  | LR a x b
  | RR a x b
  | V (B a x b)
  | V (R a x b) -> RBTree (B a x b)

val insert_mem : x:int -> s:rbtree ->
  Lemma (forall y. mem y s.root \/ y = x <==> mem y (insert x s).root)
let insert_mem x s = ins_mem x s.root

///
/// Unit tests
///

let sanity_check1 : rbtree =
  let t = B (B Leaf 2 Leaf) 5 (B Leaf 8 Leaf) in
  assert_norm (sorted t);
  RBTree t

[@expect_failure]
let sanity_check2 : rbtree =
  let t = B (B Leaf 8 Leaf) 5 (B Leaf 2 Leaf) in
  assert_norm (~(sorted t));
  RBTree t

let rec repeat s (n:nat) = 
  match n with
  | 0 -> ""
  | n -> s ^ repeat s (n-1)

let node_to_string b c indent s =
  let node = function
    | Red   -> "○"
    | Black -> "●"
  in
  indent ^ b ^ node c ^ s ^ "\n"

val rbnode_to_string: #h:nat -> #c:color -> b:string -> h0:nat{h <= h0} -> root:rbnode h c 
  -> Tot string (decreases root)
let rec rbnode_to_string #h #c b h0 root = 
  let indent = repeat "     " (h0 - h) in
  match root with
  | Leaf -> node_to_string b Black indent ""
  | R left v right ->
    rbnode_to_string "┌─" (h0+1) left ^
    node_to_string b c indent (string_of_int v ^ (if v < 10 then " " else "") ^ "┤") ^
    rbnode_to_string "└─" (h0+1) right
  | B left v right ->
    rbnode_to_string "┌─" h0 left ^
    node_to_string b c indent (string_of_int v ^ (if v < 10 then " " else "") ^ "┤") ^
    rbnode_to_string "└─" h0 right

let rbtree_to_string t =
  rbnode_to_string "──" t.h t.root

let rec loop (t:rbtree) : All.ML unit =
  IO.print_string (rbtree_to_string t);
  IO.print_string "Insert> ";
  let i = IO.input_int () in  
  let u = insert i t  in
  loop u

let test () = loop (RBTree Leaf)


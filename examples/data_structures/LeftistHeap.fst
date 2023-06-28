(*
   Copyright 2023 Microsoft Research
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

module LeftistHeap

// -----------------------------------------------------------------
// Elimination rules for the ordered type class, and instantiations
// -----------------------------------------------------------------

let gt (#t: eqtype) {| _ : ordered t |} (a b: t) =
  leq b a && a <> b

let transitivity #a {| p : ordered a |} (x y z: a):
  Lemma (requires leq x y /\ leq y z)
  (ensures leq x z)
= p.properties

let reflexivity #a {| p : ordered a |} (x: a):
  Lemma (ensures leq x x)
= p.properties

let antisymmetry (#a: eqtype) {| p : ordered a |} (x y: a):
  Lemma (requires leq x y /\ leq y x) (ensures x = y)
= p.properties

let total_order (#a: eqtype) {| p : ordered a |} (x y: a):
  Lemma (ensures leq x y \/ leq y x)
= p.properties

instance ints_leq : ordered int =
{
  leq = (<=);
  properties = ()
}

instance nats_leq : ordered nat =
{
  leq = (<=);
  properties = ()
}

// -----------------------------------------------------------------
// Useful functions and lemmas for lists
// -----------------------------------------------------------------

let delta (#a: eqtype) (x y:a): GTot int = (if x = y then 1 else 0)

let rec count (#a: eqtype) (l: list a) y: GTot nat =
  match l with
  | [] -> 0
  | t::q -> delta t y + count q y

let rec lower_bounded #a {| _ : ordered a |} (l: list a) m: GTot bool =
  match l with
  | [] -> true
  | t::q -> leq m t && lower_bounded q m

let rec lower_bounded_trans #a {| _ : ordered a |} (l: list a) m1 m2:
  Lemma (requires lower_bounded l m1 /\ leq m2 m1) (ensures lower_bounded l m2)
= match l with
  | [] -> ()
  | t::q -> (transitivity m2 m1 t; lower_bounded_trans q m1 m2)

let rec sorted_then_lower_bounded #a {| _ : ordered a |} (t: a) (q: list a):
  Lemma (requires sorted (t::q)) (ensures lower_bounded (t::q) t)
= match q with
  | [] -> reflexivity t
  | a::b ->
    (if Cons? b then transitivity t a (Cons?.hd b) else ();
    sorted_then_lower_bounded t b; assert (lower_bounded q t))

// Any element in the list is greater than or equal to a lower bound of the list
let rec lower_bounded_and_count (#a: eqtype) {| _ : ordered a |} (l: list a) (m x: a):
  Lemma (requires lower_bounded l m /\ count l x > 0) (ensures leq m x)
= match l with
  | [] -> ()
  | t::q -> if (t = x) then () else lower_bounded_and_count q m x

// Two sorted lists with the same elements (with the same multiplicities) are the same
#push-options "--split_queries always"
#push-options "--z3rlimit 30"
let rec injectivity_count_sorted (#t: eqtype) {| _ : ordered t |} (a b: list t):
  Lemma (requires (forall y. count a y = count b y) /\ sorted a /\ sorted b)
  (ensures a = b)
= match a, b with
  | ta::qa, tb::qb -> (
    // 1. ta <= tb
    eliminate forall y. count a y = count b y with tb;
    assert (count a tb > 0);
    sorted_then_lower_bounded ta qa;
    lower_bounded_and_count a ta tb;
    // 2. ta <= tb
    eliminate forall y. count a y = count b y with ta;
    assert (count b ta > 0);
    sorted_then_lower_bounded tb qb;
    lower_bounded_and_count b tb ta;
    // 3. induction hypothesis
    antisymmetry ta tb;
    injectivity_count_sorted #t qa qb
    )
  | _ -> ()
#pop-options
#pop-options

let rec merge_count (#t: eqtype) {| _: ordered t |} (a b: list t) y:
  Lemma (ensures count (merge a b) y = count a y + count b y)
= match a, b with
  | ta::qa, tb::qb -> if (leq ta tb) then merge_count qa b y else merge_count a qb y
  | _ -> ()

let rec sorted_merge #t {| _ : ordered t |} (a b: list t):
  Lemma (requires sorted #t a /\ sorted #t b) (ensures sorted (merge #t a b))
= match a, b with
  | ta::qa, tb::qb -> if (leq ta tb)
  then sorted_merge #t qa b
  else (sorted_merge #t a qb; total_order ta tb)
  | _ -> ()

let rec merge_lower_bounded (#t: eqtype) {| _ : ordered t |} (a b: list t) m:
  Lemma (requires lower_bounded a m /\ lower_bounded b m) (ensures lower_bounded (merge a b) m)
= match a, b with
  | ta::qa, tb::qb -> if (leq ta tb)
  then merge_lower_bounded qa b m
  else merge_lower_bounded a qb m
  | _ -> ()

// -----------------------------------------------------------------
// Useful functions and lemmas for heaps
// -----------------------------------------------------------------

type heap a =  
  | Leaf: heap a
  | Node: key:a -> left:heap a -> right:heap a -> rank:nat-> heap a

let rec size t: GTot nat =
  match t with
  | Leaf -> 0
  | Node _ l r _ -> 1 + size l + size r

// recursively updates the lower bound, as opposed to the list one
let rec lower_bounded_heap (#a: eqtype) {| _ : ordered a |} (t: heap a) (m: a): GTot bool =
  match t with
  | Leaf -> true
  | Node k l r _ -> lower_bounded_heap l k && lower_bounded_heap r k && leq m k

let heap_property (#a: eqtype) {| _ : ordered a |} (t: heap a): prop =
  match t with
  | Leaf -> True
  | Node k l r _ -> lower_bounded_heap l k /\ lower_bounded_heap r k

let rec count_heap (#a: eqtype) {| _ : ordered a |} (t: heap a) y: GTot nat =
  match t with
  | Leaf -> 0
  | Node k l r _ -> delta k y + count_heap l y + count_heap r y

// -----------------------------------------------------------------
// List representations of heaps
// -----------------------------------------------------------------

let rec to_list_aux (#a: eqtype) {| _ : ordered a |} (t: heap a): GTot (list a) =
  match t with
  | Leaf -> []
  | Node k l r _ -> k :: merge (to_list_aux l) (to_list_aux r)

// A lower bound for a heap is also a lower bound for its list representation
let rec to_list_aux_lower_bounded (#a: eqtype) {| _ : ordered a |} (t: heap a) m:
  Lemma (requires lower_bounded_heap t m) (ensures lower_bounded (to_list_aux t) m)
= match t with
  | Leaf -> ()
  | Node k l r _ -> (
    to_list_aux_lower_bounded l k;
    lower_bounded_trans (to_list_aux l) k m;
    to_list_aux_lower_bounded r k;
    lower_bounded_trans (to_list_aux r) k m;
    merge_lower_bounded (to_list_aux l) (to_list_aux r) m
  )

// The list representation of a sorted heap is sorted
let rec heap_property_then_sorted (#a: eqtype) {| _ : ordered a |} (t: heap a):
  Lemma (requires heap_property t) (ensures sorted (to_list_aux t))
= match t with
  | Node k l r _ ->
    (
      heap_property_then_sorted l;
      heap_property_then_sorted r;
      sorted_merge (to_list_aux l) (to_list_aux r)
    )
  | _ -> ()

let rec count_list_heap (#a: eqtype) {| _ : ordered a |} (t: heap a) y:
  Lemma (ensures count_heap t y = count (to_list_aux t) y)
= match t with
  | Leaf -> ()
  | Node k l r _ -> (count_list_heap l y; count_list_heap r y;
    merge_count (to_list_aux l) (to_list_aux r) y)

// -----------------------------------------------------------------
// Merging heaps
// -----------------------------------------------------------------

// Termination measure
let measure (#a: eqtype) {| _ : ordered a |} (t1 t2: heap a) =
  match t1, t2 with
  | Node _ _ _ _, Leaf -> 1
  | Node k1 _ _ _, Node k2 _ _ _ -> if gt k1 k2 then 1 else 0
  | _ -> 0

let rank t =
  match t with
  | Leaf -> 0
  | Node _ _ _ r -> r

let rec merge_heaps_aux (#a: eqtype) {| _ : ordered a |}  (t1 t2: heap a):
  Tot (heap a)
  (decreases %[size t1 + size t2; measure t1 t2])
  =
  match t1, t2 with
  | Leaf, _ -> t2
  | _, Leaf -> t1
  | Node k1 l r _, Node k2 _ _ _ ->
  if gt k1 k2 then merge_heaps_aux t2 t1
  else
    let merged = merge_heaps_aux r t2 in
    let rank_left = rank l in
    let rank_right = rank merged in
    if rank_left >= rank_right then
      Node k1 l merged (rank_right + 1)
    else
      Node k1 merged l (rank_left + 1)

// -----------------------------------------------------------------
// Merging heaps preserves sortedness and the elements
// -----------------------------------------------------------------

let rec heap_property_merge #a {| _ : ordered a |} (t1 t2: heap a): Lemma
  (requires heap_property t1 /\ heap_property t2)
  (ensures heap_property (merge_heaps_aux t1 t2))
  (decreases %[size t1 + size t2; measure t1 t2])
= match t1, t2 with
  | Node k1 l r _, Node k2 _ _ _ ->
  if gt k1 k2 then heap_property_merge t2 t1
  else (heap_property_merge r t2; total_order k1 k2)
  | _ -> ()

let rec count_merge_aux (#a: eqtype) {| _ : ordered a |} (t1 t2: heap a) y:
  Lemma (ensures count_heap (merge_heaps_aux t1 t2) y = count_heap t1 y + count_heap t2 y)
  (decreases %[size t1 + size t2; measure t1 t2])
= match t1, t2 with
  | Node k1 l r _, Node k2 _ _ _ ->
  if gt k1 k2 then count_merge_aux t2 t1 y
  else count_merge_aux r t2 y
  | _ -> ()

let merge_heap_charact (#t: eqtype) {| _ : ordered t |} (a b: heap t):
  Lemma (requires heap_property a /\ heap_property b)
  (ensures to_list_aux (merge_heaps_aux a b) = merge (to_list_aux a) (to_list_aux b))
= 
  let l1 = to_list_aux (merge_heaps_aux a b) in
  let l2 = merge (to_list_aux a) (to_list_aux b) in
  (
    // Step 1: (forall y. count l1 y = count l2 y);
    introduce forall (y: t). (count l1 y = count l2 y) with (
      calc (=) {
        count l1 y;
        = {count_list_heap (merge_heaps_aux a b) y}
        count_heap (merge_heaps_aux a b) y;
        = {count_merge_aux a b y}
        count_heap a y + count_heap b y;
        = {count_list_heap a y; count_list_heap b y}
        count (to_list_aux a) y + count (to_list_aux b) y;
        = {merge_count (to_list_aux a) (to_list_aux b) y}
        count l2 y;
      }
    );
    // Step 2: l1 is sorted
    heap_property_merge a b;
    heap_property_then_sorted (merge_heaps_aux a b);
    // Step 3: l2 is sorted
    heap_property_then_sorted a;
    heap_property_then_sorted b;
    sorted_merge (to_list_aux a) (to_list_aux b);
    // Step 4: Conclusion
    injectivity_count_sorted l1 l2
)

// -----------------------------------------------------------------
// Merging heaps preserves the properties about ranks
// -----------------------------------------------------------------

// leftist property: Left ranks are always greater than or equal to right ranks
let rec leftist_property t: GTot bool =
  match t with
  | Leaf -> true
  | Node _ l r _ -> leftist_property l && leftist_property r && rank l >= rank r

// The rank of a node is the length of its rightmost spine
let rec compute_rank t: GTot int =
  match t with
  | Leaf -> 0
  | Node _ l r _ -> 1 + compute_rank r

// The annotated rank corresponds to the real (computed) rank
let rec correct_ranks t: GTot bool =
  match t with
  | Leaf -> true
  | Node _ l r rk -> correct_ranks l && correct_ranks r && rk = compute_rank t

// the merging heaps function correctly modifies the annotated ranks
let rec correct_ranks_merge (#a: eqtype) {| _ : ordered a |} (t1 t2: heap a): Lemma
  (requires correct_ranks t1 && correct_ranks t2)
  (ensures correct_ranks (merge_heaps_aux t1 t2))
  (decreases %[size t1 + size t2; measure t1 t2])
= match t1, t2 with
  | Node k1 l r _, Node k2 _ _ _ ->
  if gt k1 k2 then correct_ranks_merge t2 t1
  else correct_ranks_merge r t2
  | _ -> ()

let rec leftist_property_merge (#a: eqtype) {| _ : ordered a |} (t1 t2: heap a): Lemma
  (requires leftist_property t1 && leftist_property t2)
  (ensures leftist_property (merge_heaps_aux t1 t2))
  (decreases %[size t1 + size t2; measure t1 t2])
= match t1, t2 with
  | Node k1 l r _, Node k2 _ _ _ ->
  if gt k1 k2 then leftist_property_merge t2 t1
  else leftist_property_merge r t2
  | _ -> ()

// -----------------------------------------------------------------
// Actual implementation of the interface
// -----------------------------------------------------------------

let leftist (a: eqtype) {| _ : ordered a |} =
  t:heap a{heap_property t /\ leftist_property t /\ correct_ranks t}

let to_list (#a: eqtype) {| _ : ordered a |} (t:leftist a): GTot (l:list a{sorted l}) =
  (heap_property_then_sorted t; to_list_aux t)

let empty (#a: eqtype) {| _ : ordered a |}: (t:leftist a{ to_list t = [] }) = Leaf

let isEmpty (#a: eqtype) {| _ : ordered a |} (t:leftist a): (b:bool{ b <==> to_list t = []}) = Leaf? t

let singleton (#a: eqtype) {| _ : ordered a |} (k:a): (s:leftist a{to_list s = [k]}) =
  Node k Leaf Leaf 1

let merge_heaps (#a: eqtype) {| _ : ordered a |} (t1 t2: leftist a):
  (t:leftist a{ to_list t = merge (to_list t1) (to_list t2) })
= (merge_heap_charact t1 t2;
  heap_property_merge t1 t2;
  leftist_property_merge t1 t2;
  correct_ranks_merge t1 t2;
  merge_heaps_aux t1 t2)

let insert (#a: eqtype) {| _ : ordered a |} (x: a) (t:leftist a):
  (t':leftist a{ to_list t' = merge [x] (to_list t) })
= merge_heaps (singleton x) t

let get_min (#a: eqtype) {| _ : ordered a |} (t:leftist a{ ~(isEmpty t) }):
  (x:a{ x = Cons?.hd (to_list t) }) =
  match t with
  | Node k _ _ _ -> k

let delete_min (#a: eqtype) {| _ : ordered a |} (t: leftist a{~(isEmpty t)}):
  (t':leftist a{to_list t' = Cons?.tl (to_list t) }) =
  match t with
  | Node _ l r _ -> merge_heaps l r
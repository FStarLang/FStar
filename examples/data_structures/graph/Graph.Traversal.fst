module Graph.Traversal

open Graph.Base
open Seq.Complements
module SEM = FStar.StrongExcludedMiddle
module S = FStar.Seq
module C = FStar.Classical

(* `depth g root x d` holds iff the depth of x in the graph rooted in root is d *)
(* where None = \infty *)
let depth (#n:nat) (g:graph0 n) (root x:_in g) (d:option nat) =
  match d with
  | None -> (forall (p:path g). from p == root ==> to p =!= x)
  | Some k ->
    (exists (p:path g). from p == root /\ to p == x /\ length p == k) /\
    (forall (p:path g). from p == root /\ to p == x ==> length p >= k)

let lemma_path_max_length (#n:nat) (g:graph0 n) (root x : _in g)
  : Lemma (requires (forall (p:path g). from p == root /\ to p == x ==> length p >= n+1))
          (ensures (forall (p:path g). from p == root ==> to p =!= x))
(* TODO : prove me ! *)
= admit ()

let rec depth_fun_aux (#n:nat) (g:graph0 n) (root x:_in g) (k:nat)
  : Ghost (option nat)
    (requires (forall (p:path g). from p == root /\ to p == x ==> length p >= k))
    (ensures (depth g root x))
    (decreases (n+1-k))
= if k > n then (lemma_path_max_length g root x ; None)
  else if SEM.strong_excluded_middle (exists (p:path g). from p == root /\ to p == x /\ length p == k)
  then Some k
  else depth_fun_aux g root x (k+1)

let depth_fun (#n:nat) (g:graph0 n) (root x:_in g) : GTot (d:option nat{depth g root x d}) =
  depth_fun_aux g root x 0


let traversal (#n:nat) (g:graph0 n) (root:_in g) (s: nodesetseq n) :Type0 =
    S.length s > 0 /\
    (forall (i:_in s).
      (i == 0 ==> s @^ i == root) /\
      (i =!= 0 ==> (exists (j:_in s). j < i /\ is_in_graph (s @^ j) (s @^ i) g)))


let inv (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat) =
  i <= S.length ns /\ S.length ps == S.length ns /\
  (forall (ind:nat). ind < i ==>  (let p = (ps @^ ind) in from p == root /\ to p == (ns @^ ind)))

#set-options "--detail_errors"

let false_elim (#a:Type) (x:unit) : Pure a (requires False) (ensures (fun _ -> True)) = match x with

let update_path_seq (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat) (p:path g)
 : Pure (S.seq (path g))
 (requires (i< S.length ns /\ traversal g root ns /\ inv g root ns ps i /\ from p == root /\ to p == (ns @^ i)))
 (ensures (ensures (fun ps -> traversal g root ns /\ inv g root ns ps (i+1))))
 = let ps' = S.upd ps i p in 
   let prop1 = (forall (ind:nat). ind < i ==>  (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in 
   let prop2= (let p = (ps' @^ i) in from p == root /\ to p == (ns @^ i)) in
   let prop3 = (forall (ind:nat). ind < (i+1) ==>  (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   assert(prop1);
   assert(prop2);
   (* NOTE THE ASSUMPTION USED HERE *)
   assume(prop1 /\ prop2 ==> prop3);
   assert(prop3);
   assert((i+1) <= S.length ns /\ S.length ps' == S.length ns /\ prop3 ==> inv g root ns ps' (i+1));
   assert(inv g root ns ps' (i+1));
   ps'


let rec traversal_construct_getpath_aux (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat)
 : Pure (S.seq (path g)) 
 (requires (traversal g root ns /\ inv g root ns ps i))
 (ensures (fun ps -> traversal g root ns /\ inv g root ns ps (S.length ns - 1)))
 (decreases (S.length ns - i))
= if i >= S.length ns - 1 then ps
  else if i = 0 then
   let ps' = update_path_seq g root ns ps i (empty_path_at g root) in 
   traversal_construct_getpath_aux g root ns ps' (i+1)
  else
   let f ind a = ind < i && is_in_graph a (ns @^ i) g in
   match index_of_l2 ns f with
   | Some v -> 
     index_of_l2_spec ns f;
     let v : nat = v in
     let pv = append1 g (ps @^ v) (empty_path_at g (ns @^ i)) in
     let ps' = update_path_seq g root ns ps i pv in
     traversal_construct_getpath_aux g root ns ps' (i+1)
   | None -> 
     assert(i =!= 0);
     assert (exists (j:_in ns). j < i /\ is_in_graph (ns @^ j) (ns @^ i) g) ;
     index_of_l2_spec ns f;
     false_elim ()

let traversal_construct_getpath (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n)
 : Pure (S.seq (path g)) 
 (requires (traversal g root ns))
 (ensures (fun ps -> traversal g root ns /\ inv g root ns ps (S.length ns - 1)))
 = 
 let ps = S.create (S.length ns) (empty_path_at g root) in
 traversal_construct_getpath_aux g root ns ps 0

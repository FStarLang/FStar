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


type traversal (#n:nat) (g:graph0 n) (root:_in g) : nodesetseq n -> Type0 =
  fun s ->
    S.length s > 0 /\
    (forall (i:_in s).
      (i == 0 ==> s @^ i == root) /\
      (i =!= 0 ==> (exists (j:_in s). j < i /\ is_in_graph (s @^ j) (s @^ i) g)))

let rec traversal_construct_getpath_aux (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n{traversal g root ns}) (ps:S.seq(path g)) (i:k:nat{k + 1< S.length ns})
 : Pure (path g) 
 (requires (S.length ps == i /\ i < S.length ns /\ (forall (ind:k:nat{k<S.length ps}). let p = (ps @^ ind) in from p == root 
 /\ to p == (ns @^ ind))))
 (ensures (fun p ->  i  < S.length ns /\ from p == root /\ to p == (S.index ns  (i + 1))))
 = let sl = S.slice ns 0 i in
 
  match index_of_l (fun a -> is_in_graph a (S.index ns (i+1)) g) sl with
   | Some v -> 
   let p1 = (ps @^ (v <: nat)) in
   let p2 = S.create 1 (ns @^ (v <: nat)) in let p2' = S.append p2 (S.create 1 (ns @^ (i + 1))) in
   index_of_l_spec (fun a -> is_in_graph a (S.index ns (i+1)) g) sl;
   assert(valid_path g p2');
   let p' = append g p1 p2' in  assert(valid_path g p'); assert(from p' == root); assert(to p' == (S.index ns (i + 1)));  p'
   | None -> if i = 0 then admit() 
   else 
   (

   (* This assertion right here is the one that fails. I am trying to prove a contradiction in this case*)
   assert((forall (i':_in ns).
      (i' == 0 ==> ns @^ i' == root) /\
      (i' =!= 0 ==> (exists (j:_in ns). j < i' /\ is_in_graph (ns @^ j) (ns @^ i') g)))); admit();
   assert(exists (j:_in ns). j < (i+1) /\ is_in_graph (ns @^ j) (ns @^ (i + 1)) g); admit()
   )
    

let rec traversal_construct (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n{traversal g root ns}) (ps:S.seq(path g)) (i:nat)
 : Pure (S.seq (path g)) 
 (requires (S.length ps == i /\ i < S.length ns /\ (forall (ind:k:nat{k<S.length ps}). let p = (ps @^ ind) in from p == root /\ to p == (ns @^ ind))))
 (ensures (fun x -> S.length x == i /\ i <= S.length ns /\ (forall (ind:k:nat{k<S.length x}). let p = (x @^ ind) in from p == root /\ to p == (ns @^ ind))))
 (decreases (S.length ns - i))
 = match S.length ns - i with
   | 0 -> ps
   | x -> 
     begin match index_of_l (fun a -> is_in_graph (ns @^ a) (ns @^ (i+1))) (S.slice s 0 i) with
      | Some v -> admit()
      | None -> admit()
     end
   traversal_construct g root ns ps (i+1)

// let rec traversal_reachability
//   (#n:nat)
//   (g:graph0 n)
//   (root:_in g)
//   (ns:nodesetseq n {traversal g root ns})
//   : Lemma (requires True)
//     (ensures (forall (i:_in ns). reachable g root (ns @^ i)))
// =
//   let reachable_aux (*(nss:nodesetseq n{traversal g root ns})*)
//     (w:squash(True))
//     (x:_in ns)
//     : Lemma (reachable g root (ns @^ x))
//   =
//     FStar.Squash.give_proof w ;
//     match x with
//     | 0 -> let p = empty_path_at g (ns @^ 0) in ()
//     | e ->  assert(e =!= 0); assert(traversal g root ns);

//     (*Why is this assert failing?*)
//     assert (traversal g root ns) ;
//     assert(S.length ns > 0 /\ S.head ns == root /\
//       (forall (i:_in ns). i == 0 \/ (exists (h:k:nat{k<i}). is_in_graph (ns @^ h) (ns @^ i) g)));
//     admit();
//     assert(forall (i:_in ns). i == 0 \/ (exists (h:k:nat{k<i}). is_in_graph (ns @^ h) (ns @^ i) g));
//     admit();
//     assert((exists (w:k:nat{k < e}). is_in_graph (ns @^ w) (ns @^ e) g)); admit()
//   in
//   C.forall_intro (reachable_aux (FStar.Squash.get_proof (True)))


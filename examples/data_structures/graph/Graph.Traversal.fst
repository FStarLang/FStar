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


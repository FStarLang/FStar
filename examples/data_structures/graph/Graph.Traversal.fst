module Graph.Traversal

open Graph.Base
open Seq.Complements
module SEM = FStar.StrongExcludedMiddle
module S = FStar.Seq
module C = FStar.Classical
open FStar.Tactics

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

(*#set-options "--detail_errors"*)

let false_elim (#a:Type) (x:unit) : Pure a (requires False) (ensures (fun _ -> True)) = match x with

let conj_arg (#a #b #c:Type) (_:squash (a /\ b)) (_:squash (a /\ b ==> c))
  : Lemma c
=  ()


let inv2 (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat) =
  i <= S.length ns /\ S.length ps == S.length ns /\
  (forall (ind:k:nat{k<i}). (let p = (ps @^ ind) in from p == root /\ to p == (ns @^ ind)))

let update_path_seq (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat) (p:path g)
 : Pure (S.seq (path g))
 (requires (i< S.length ns /\ traversal g root ns /\ inv2 g root ns ps i /\ from p == root /\ to p == (ns @^ i)))
 (ensures (ensures (fun ps -> traversal g root ns /\ inv2 g root ns ps (i+1))))
 = let ps' = S.upd ps i p in
   let prop1 = (forall (ind:k:nat{k < i}). (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   let prop2= (let p = (ps' @^ i) in from p == root /\ to p == (ns @^ i)) in
   let prop3 = (forall (ind:k:nat{k<(i+1)}). (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   
   assert(prop1);
   assert(prop2);
   admit();
   (* NOTE THE ASSUMPTION USED HERE *)
   assert((prop1 /\ prop2) ==> prop3);
   admit();
   (*assert(prop3);
   assert((i+1) <= S.length ns /\ S.length ps' == S.length ns /\ prop3 ==> inv g root ns ps' (i+1));
   assert(inv g root ns ps' (i+1));*)
   ps'


let less_or_eq (i:nat) (x:nat) = x < i \/ x == i
let less_or_eq_proof (i:nat) (x:nat) (w:squash(x < i+1)) : Lemma (less_or_eq i x) =
 ()

let split_arg (#a #b #c:Type) (_:squash (a \/ b)) (_:squash (a ==> c)) (_:squash (b ==> c))
  : Lemma c
=  ()

let apply_to_binders (t:term) (bs:binders) =
  List.Tot.fold_left (fun t b -> pack (Tv_App t (pack (Tv_Var b)))) t bs

(*let test (t:tactic term) (bs:binders) : tactic term = t0 <-- t ; return (apply_to_binders t0 bs)*)

let term_of_binder b = pack (Tv_Var b)
let apply_term t ts = List.Tot.fold_left (fun t1 t2 -> pack (Tv_App t1 t2)) t ts


(*let update_path_seq (#n:nat) (g:graph0 n) (root:_in g) (ns : nodesetseq n) (ps:S.seq (path g)) (i:nat) (p:path g)
 : Pure (S.seq (path g))
 (requires (i< S.length ns /\ traversal g root ns /\ inv g root ns ps i /\ from p == root /\ to p == (ns @^ i)))
 (ensures (ensures (fun ps -> traversal g root ns /\ inv g root ns ps (i+1))))
 = let ps' = S.upd ps i p in
   let prop1 = (forall (ind:nat). ind < i ==>  (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   let prop2= (let p = (ps' @^ i) in from p == root /\ to p == (ns @^ i)) in
   let prop3 = (forall (ind:nat). ind < (i+1) ==>  (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   let prop4 = prop1 /\ prop2 ==> prop3 in
   let open FStar.Squash in
   let p1 = get_proof prop1 in
   let p2 = get_proof prop2 in
   let asst = assert_by_tactic
   (dump "A0" ;;
     i0 <-- forall_intro ;
     hi0 <-- implies_intro ;
    dump "A1" ;;
    t <--  quote (less_or_eq i) ;
    hx <--  tcut (apply_to_binders t [i0]) ;
    t <--  quote split_arg ;
    apply_lemma (return (apply_to_binders t [hx])) ;;
    dump "C" ;;
    exact (quote p1) ;;
    exact (quote p2) ;;
    
    t0 <--  quote (less_or_eq_proof i) ;
    apply_lemma (return (apply_to_binders t0 [i0 ; hi0])) ;;
    //   dump "A2";;
    // apply_lemma (quote (less_or_eq_proof i)) ;;
    //   dump "A3" ;;
    // exact (return (term_of_binder i0)) ;;
    //   dump "A4" ;;
    fail "wtf"
    // apply_lemma (quote_lid []) ;;
    //   dump "A5" ;; fail "wtf"
(*    apply_lemma (quote_lid ["Test";"psi_false"])*)
    )
  (forall (ind:nat). ind < (i+1) ==>  (let p = (ps' @^ ind) in from p == root /\ to p == (ns @^ ind))) in
   
   admit();
   (* NOTE THE ASSUMPTION USED HERE *)
   (*assume(prop1 /\ prop2 ==> prop3);*)
   (*assert(prop3);
   assert((i+1) <= S.length ns /\ S.length ps' == S.length ns /\ prop3 ==> inv g root ns ps' (i+1));
   assert(inv g root ns ps' (i+1));*)
   ps'
*)

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

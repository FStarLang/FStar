module Graph.Base

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical

let graph0 (n:nat) = s:S.seq (list (fin n)){S.length s == n}

let no_self_loop (#n:nat) (g:graph0 n) =
  forall (i:_in g). not (L.mem (i <: fin n) (g @^ i))

let no_parallel_edge (#n:nat) (g:graph0 n) =
  forall (i:_in g). L.noRepeats (g @^ i)

let undirected (#n:nat) (g:graph0 n) =
  forall (i:_in g) (k:fin n). L.mem k (g @^ i) ==> i < k

let undirected_graph (n:nat) = g:graph0 n{no_self_loop g /\ no_parallel_edge g /\ undirected g}

let node_size (#n:nat) (g:graph0 n) = S.length g

let edge_size (#n:nat) (g:graph0 n) =
  L.fold_left (+) 0 (L.map L.length (S.seq_to_list g))

let prepath (n:nat) = S.seq (fin n)

let valid_path (#n:nat) (g:graph0 n) (p:prepath n) =
  S.length p > 0 /\ (forall (i:nat{i < S.length p - 1}). L.mem (p @^ i+1) (g @^ p @^ i))

let path (#n:nat) (g:graph0 n) = p:prepath n{valid_path #n g p}

let from (#n:nat) (#g:graph0 n) (p:path g) = S.head p
let to (#n:nat) (#g:graph0 n) (p:path g) = S.last p

let empty_path_at (#n:nat) (g:graph0 n) (i:_in g) : path g =
  S.create 1 i

let elementary (#n:nat) (p:prepath n) = forall (i j : _in p) . p @^ i == p @^ j ==> i == j

let length (#n:nat) (p:prepath n) = S.length p

let prefix (#n:nat) (p1 p2:prepath n) = length p1 <= length p2 /\ (forall (i:_in p1). p1 @^ i == p2 @^ ((i <: nat) <: _in p2))

let elementary_cycle (#n:nat) (#g:graph0 n) (p:path g) = elementary (S.slice p 1 (length p)) /\ from p == to p

val is_in_graph : (#n:nat) -> (a:fin n) -> (b:fin n) -> (g : graph0 n) -> Tot bool
let is_in_graph #n a b g = L.mem b (g @^ a)



val lemma_valid_subpath_is_valid : (#n:nat) -> (g:graph0 n) -> (p:path g) -> (a:_in p) -> (b:_in p)
 -> Lemma (requires (a <= b))
         (ensures (a <= b /\ valid_path g (S.slice p a (b + 1))))
let lemma_valid_subpath_is_valid #n g p a b =
  assert (forall (i:nat{0 <= i /\ i < b - a}). is_in_graph (p @^ (a+i)) (p @^ (a+i+1)) g);
  let p' = S.slice p a (b+1) in
  assert (forall (i:nat{0 <= i /\ i < b - a}). is_in_graph (p' @^ i) (p' @^ (i+1)) g)

let lemma_elementary_slice (#n:nat) (p:prepath n) (i j : k:nat{k <= S.length p})
  : Lemma (requires (i <= j /\ elementary p))
    (ensures (i <= j /\ elementary (S.slice p i j)))
= let p' = S.slice p i j in
  assert (forall (i0 j0: _in p'). p @^ (i+i0) == p @^ (i+j0) ==> i0 == j0)


let lemma_snoc_elementary (#n:nat) (p:prepath n) (e:fin n)
 : Lemma(requires (elementary p /\ index_of e p == None))
   (ensures (elementary (S.snoc p e)))
= let p' = S.append p (S.create 1 e) in
  S.lemma_eq_elim (S.snoc p e) (S.append p (S.create 1 e));
  assert(forall (i0 j0 : k:nat{k<S.length p}). p @^ i0 == p @^ j0 ==> i0 == j0);
  assert(forall (i0 j0 : k:nat{k<S.length p}). p' @^ i0 == p' @^ j0 ==> i0 == j0);
  count_zero_none e p;
  assert(forall (i0 : k:nat{k<S.length p}) . ~(p' @^ i0 == p' @^ (S.length p' - 1)))


(*TODO: Prove that this holds for any ordering *)
val lemma_mutually_exclusive_elementary_append : (#n:nat) -> (p1:prepath n) -> (p2:prepath n) ->
 Lemma (requires (disjoint p1 p2 /\ elementary p1 /\ elementary p2))
  (ensures (elementary (S.append p1 p2)))
  (decreases (S.length p2))
let rec lemma_mutually_exclusive_elementary_append #n p1 p2 =
 match S.length p2 with
 | 0 -> S.lemma_eq_elim p1 (S.append p1 p2)
 | x ->
   let p1' = (S.snoc p1 (S.head p2)) in
   let p2' = S.tail p2 in
   assert(forall (j: k:_in p2{k>0}) . ~(p2 @^ j == p2 @^ 0));
   assert(forall (j:_in p2'). (p2' @^ j == p2 @^ (j + 1)));
   lemma_disjoint_append p1 (S.create 1 (S.head p2)) p2';
   lemma_snoc_elementary p1 (S.head p2);
   S.lemma_eq_elim (S.append p1 p2) (S.append p1' p2');
   lemma_mutually_exclusive_elementary_append p1' p2'

let rec to_elementary_path_aux (#n:nat) (g:graph0 n) (p:path g) (pn : path g) (i: k:nat{k<=S.length p})
 : Pure (path g)
 (requires (S.length p - i >= 1 /\ elementary pn /\ 
  (disjoint pn (S.slice p i (S.length p))) /\
  (S.length pn == 0 \/ is_in_graph (S.last pn) (S.head (S.slice p i (S.length p))) g)
  ))
 (ensures (fun p' -> elementary p'))
 (decreases (S.length p - i)) =
 let remaining = S.slice p i (S.length p) in
 begin match S.length remaining with
 | 1 ->
   lemma_mutually_exclusive_elementary_append pn remaining;
   S.append pn remaining
 | x ->
   begin match index_of (S.head remaining) (S.tail remaining) with
   | None ->
     let pn' = (S.snoc pn (S.head remaining)) in
     let remaining' = S.tail remaining in
     let head_seq = S.create 1 (S.head remaining) in
     lemma_disjoint_slice pn remaining 0 1;
     S.lemma_eq_elim (S.slice remaining 0 1) head_seq;
     lemma_mutually_exclusive_elementary_append pn head_seq;
     count_zero_none (remaining @^ 0) remaining';
     assert(forall (j:_in remaining'). (remaining' @^ j == remaining @^ (j + 1)));
     lemma_disjoint_append pn head_seq remaining';
     S.lemma_eq_elim remaining' (S.slice p (i + 1) (S.length p));
     to_elementary_path_aux g p pn' (i + 1)
   | Some v ->
     let v' = (v+1) + i in
     lemma_disjoint_slice pn remaining (v+1) (S.length remaining);
     S.lemma_eq_elim (S.slice p v' (S.length p)) (S.slice remaining (v+1) (S.length remaining));
     assert(disjoint pn (S.slice p v' (S.length p)));
     to_elementary_path_aux g p pn v'
   end
 end

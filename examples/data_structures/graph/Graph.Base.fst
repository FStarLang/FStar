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

let nodeset (n:nat) = l:list(fin n) {L.noRepeats l}

let prepath (n:nat) = S.seq (fin n)

let valid_path (#n:nat) (g:graph0 n) (p:prepath n) =
  S.length p > 0 /\ (forall (i:nat{i < S.length p - 1}). L.mem (p @^ i+1) (g @^ p @^ i))

let path (#n:nat) (g:graph0 n) = p:prepath n{valid_path #n g p}

let from (#n:nat) (#g:graph0 n) (p:path g) = S.head p
let to (#n:nat) (#g:graph0 n) (p:path g) = S.last p

let empty_path_at (#n:nat) (g:graph0 n) (i:_in g) : path g =
  S.create 1 i

let elementary (#n:nat) (p:prepath n) = forall (i j : _in p) . p @^ i == p @^ j ==> i == j

let lemma_empty_path_elementary (#n:nat) (g:graph0 n) (i:_in g)
  : Lemma (elementary (empty_path_at g i))
= ()

let length (#n:nat) (p:prepath n) = S.length p

let prefix (#n:nat) (p1 p2:prepath n) = length p1 <= length p2 /\ (forall (i:_in p1). p1 @^ i == p2 @^ ((i <: nat) <: _in p2))

let elementary_cycle (#n:nat) (#g:graph0 n) (p:path g) = elementary (S.slice p 0 (length p - 1)) /\ from p == to p

val is_in_graph : (#n:nat) -> (a:fin n) -> (b:fin n) -> (g : graph0 n) -> Tot bool
let is_in_graph #n a b g = L.mem b (g @^ a)

let mon (#n #m : nat) (f:fin n -> fin m) = forall (i j: fin n). i < j ==> f i < f j
let mon' (p q : S.seq 'a) (f:_in p -> _in q) = mon #(S.length p) #(S.length q) f

let subpath (#n:nat) (p1:prepath n) (p2:prepath n) (f: (_in p1 -> _in p2) {mon' p1 p2 f})
 = forall (i:_in p1) . p1 @^ i == p2 @^ (f i)

let slice_subpath_fun (#n:nat) (p:prepath n) (a: k:nat { k<=S.length p})
 (b: k:nat { a <= k /\ k<=S.length p}) = fun (i : _in (S.slice p a b)) -> (i + a <: _in p)

let lemma_slice_is_subpath  (#n:nat) (p:prepath n) (a: k:nat { k<=S.length p})
 (b: k:nat { a <= k /\ k<=S.length p})
 : Lemma (requires True)
         (ensures (subpath (S.slice p a b) p (slice_subpath_fun p a b)))
         = ()

val lemma_valid_csubpath_is_valid : (#n:nat) -> (g:graph0 n) -> (p:path g) -> (a:_in p) -> (b:_in p)
 -> Lemma (requires (a <= b))
         (ensures (a <= b /\ valid_path g (S.slice p a (b + 1))))
let lemma_valid_csubpath_is_valid #n g p a b =
  assert (forall (i:nat{0 <= i /\ i < b - a}). is_in_graph (p @^ (a+i)) (p @^ (a+i+1)) g);
  let p' = S.slice p a (b+1) in
  assert (forall (i:nat{0 <= i /\ i < b - a}). is_in_graph (p' @^ i) (p' @^ (i+1)) g)


let adjacent (#n:nat) (g:graph0 n) (node1 node2:fin n) = L.mem node2 (g @^ node1)

(* KM : do we really need the first part ? Wouldn't the trivial path [node1] satisfythe second part ? *)
let reachable (#n:nat) (g:graph0 n) (node1 node2:fin n) =
  exists (p : path g) . (from p == node1 /\ to p == node2)

let append (#n:nat) (g:graph0 n) (p1 p2:path g)
 : Pure (path g)
 (requires (to p1 == from p2))
 (ensures (fun p' -> from p1 == from p' /\ to p2 == to p'))
 = S.append p1 (S.slice p2 1 (S.length p2))

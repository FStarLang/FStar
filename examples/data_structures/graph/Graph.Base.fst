module Graph.Base

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements

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

let elementary (#n:nat) (p:prepath n) = L.noRepeats (S.seq_to_list p)

let length (#n:nat) (p:prepath n) = S.length p

let prefix (#n:nat) (p1 p2:prepath n) = length p1 <= length p2 /\ (forall (i:_in p1). p1 @^ i == p2 @^ ((i <: nat) <: _in p2))

let elementary_cycle (#n:nat) (#g:graph0 n) (p:path g) = elementary (S.slice p 1 (length p)) /\ from p == to p

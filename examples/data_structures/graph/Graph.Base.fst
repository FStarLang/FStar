module Graph.Base

module S = FStar.Seq
module L = FStar.List
open FStar.Fin

let _in (s:S.seq 'a) = k:nat{k < S.length s}

let graph0 (n:nat) = s:S.seq (list (fin n)){S.length s == n}

let no_self_loop (#n:nat) (g:graph0 n) =
  forall (i:_in g). not (L.mem (i <: fin n) (S.index g i))

let no_parallel_edge (#n:nat) (g:graph0 n) =
  forall (i:_in g). L.noRepeats (S.index g i)

let undirected (#n:nat) (g:graph0 n) =
  forall (i:_in g) (k:fin n). L.mem k (S.index g i) ==> i < k

let graph (n:nat) = g:graph0 n{no_self_loop g /\ no_parallel_edge g /\ undirected g}

let node_size (#n:nat) (g:graph0 n) = S.length g

let edge_size (#n:nat) (g:graph0 n) =
  L.fold_left (+) 0 (L.map L.length (S.seq_to_list g))


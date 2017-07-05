module Graph.Search

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical
open Graph.Base
open List.Complements
module N = Graph.NodeSet

let lemma_reachable_trans (#n:nat) (g:graph0 n) (n1 n2 n3:fin n)
 : Lemma (requires (reachable g n1 n2) /\ (reachable g n2 n3))
 (ensures (reachable g n1 n3))
 = 
   let aux (p1 p2 : path g) : Lemma (requires (from p1 == n1 /\ to p1 == n2) /\ (from p2 == n2 /\ to p2 == n3) ) (ensures (reachable g n1 n3)) =
     let _ = append g p1 p2 in ()
   in
   C.forall_to_exists_2 (fun (p1:path g) -> C.move_requires (aux p1))



let rec bfs (#n:nat) (g:graph0 n{no_parallel_edge g}) (s:nodeset n) (f:nodeset n)
 : Pure (nodeset n)
 (requires (True) 
  /\ N.disjoint s f)
 (ensures (fun p' -> True ))
 (decreases %[n - L.length  s])
 = match f with
 | [] -> s
 | hd :: tl ->
  let cn = hd in
  let adj = g @^ cn in
  let adj_unscene = L.filter (fun n -> L.mem n s = false && L.mem n f = false) adj in
  noRepeats_filter (fun n -> L.mem n s = false && L.mem n f = false) adj;
  let s' = hd :: s in
  let f' = N.append tl adj_unscene in
  N.lemma_disjoint_append tl adj_unscene s';
  noRepeats_length_lemma (s');
  bfs g s' f'




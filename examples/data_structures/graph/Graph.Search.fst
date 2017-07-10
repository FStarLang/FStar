module Graph.Search

module S = FStar.Seq
module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical
open Graph.Base
module LC = List.Complements
module N = Graph.NodeSet
module M = FStar.Map
module MC = Map.Complements
module SE = FStar.Set
module SEC = Set.Complements

let lemma_reachable_trans (#n:nat) (g:graph0 n) (n1 n2 n3:fin n)
 : Lemma (requires (reachable g n1 n2) /\ (reachable g n2 n3))
 (ensures (reachable g n1 n3))
 =
   let aux (p1 p2 : path g) : Lemma (requires (from p1 == n1 /\ to p1 == n2) /\ (from p2 == n2 /\ to p2 == n3) ) (ensures (reachable g n1 n3)) =
     let _ = append g p1 p2 in ()
   in
   C.forall_to_exists_2 (fun (p1:path g) -> C.move_requires (aux p1))



let rec bfs_aux (#n:nat) (g:graph0 n{no_parallel_edge g}) (s:nodeset n) (f:nodeset n)
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
  let neither_in_s_nor_f n = not (L.mem n s) && not (L.mem n f) in
  let adj_unscene = L.filter neither_in_s_nor_f adj in
  LC.noRepeats_filter neither_in_s_nor_f adj;
  let s' = hd :: s in
  let f' = N.append tl adj_unscene in
  N.lemma_disjoint_append tl adj_unscene s';
  LC.noRepeats_length_lemma (s');
  bfs_aux g s' f'

let bfs (#n:nat) (g:graph0 n{no_parallel_edge g}) (node : fin n) =
  let adj = g @^ node in
  let adj_unscene = L.filter (fun n -> not (n = node)) adj in
  LC.noRepeats_filter (fun n -> not (n = node)) adj;
  bfs_aux g [node] adj_unscene


let decrease_clause (n:nat) (s:nodeset n) : nat = LC.noRepeats_length_lemma s ; n - L.length s

let neither_in (#n0:nat) (l1 l2: nodeset n0) n = not (L.mem n l1) && not (L.mem n l2)

let fill_map #a #b (m:M.t a b) (l:list a) (v:b) =
  L.fold_left (fun acc i -> M.upd acc i v) m l

let fill_map_eq_lemma #a #b (m:M.t a b) (l:list a) (v:b)
 : Lemma (requires True) (ensures (fill_map m l v == L.fold_left (fun acc i -> M.upd acc i v) m l))
 = ()

let rec bfs_map_aux (#n:nat) (g:graph0 n{no_parallel_edge g}) (seen:nodeset n) (frntr:nodeset n) (parents:M.t (fin n) (fin n))
 : Pure (nodeset n * M.t (fin n) (fin n))
 (requires  N.disjoint seen frntr)
 (ensures (fun p' -> True ))
 (decreases (decrease_clause n seen))
= match frntr with
  | [] -> seen, parents
  | hd :: tl ->
    let adj = g @^ hd in
    let neither_in_s_nor_f = neither_in seen frntr in
    let adj_unscene = L.filter neither_in_s_nor_f adj in
    LC.noRepeats_filter neither_in_s_nor_f adj;

    let s' = hd :: seen in
    let f' = N.append tl adj_unscene in
    let p' = fill_map parents adj_unscene hd in

    N.lemma_disjoint_append tl adj_unscene s';
    bfs_map_aux g s' f' p'

let parent_map_valid (#n:nat) (g:graph0 n) (parents:M.t (fin n) (fin n)) =
  forall (x : fin n) . M.contains parents x ==>  is_in_graph (M.sel parents x) x g


let rec lemma_bfs_map_pairing_aux (#n:nat) (g:graph0 n{no_parallel_edge g}) (seen:nodeset n) (frntr:nodeset n) (parents:M.t (fin n) (fin n))
 : Lemma
   (requires
     N.disjoint seen frntr /\
     parent_map_valid g parents /\
     (forall (x: fin n) . L.mem x seen || L.mem x frntr <==> M.contains parents x))

   (ensures N.disjoint seen frntr /\
     (let s', p' = bfs_map_aux g seen frntr parents in parent_map_valid g p'))
   (decreases (decrease_clause n seen))
= match frntr with
  | [] -> ()
  | hd :: tl ->
    let adj = g @^ hd in
    let neither_in_s_nor_f = neither_in seen frntr in
    let adj_unscene = L.filter neither_in_s_nor_f adj in
    LC.noRepeats_filter neither_in_s_nor_f adj;

    let s' = hd :: seen in
    let f' = N.append tl adj_unscene in
    let p' = fill_map parents adj_unscene hd in

    N.lemma_disjoint_append tl adj_unscene s';
    LC.filter_sublist neither_in_s_nor_f adj;
    L.append_mem_forall tl adj_unscene;
    
    fill_map_eq_lemma parents adj_unscene hd;
    MC.lemma_fold_upd1 parents adj_unscene (fun _ -> hd);
    MC.lemma_fold_upd2 parents adj_unscene (fun _ -> hd);
    MC.domain_lemma parents adj_unscene (fun _ -> hd);

    SEC.as_set_mem_in_forall adj_unscene;
    lemma_bfs_map_pairing_aux g s' f' p'

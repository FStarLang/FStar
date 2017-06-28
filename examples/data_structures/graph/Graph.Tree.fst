module Graph.Tree

open Graph.Base
module S = FStar.Seq
module L = FStar.List.Tot

open Seq.Complements
open List.Complements


let connected (#n:nat) (g:graph0 n) =
  forall (i j:_in g). exists (p:path g). from p == i /\ to p == j

(* TODO : this needs to be revisited now that we changed the definition of elementarity *)
(* let non_visited_nodes (#n:nat) (g:graph0 n) (p:path g{elementary p}) : nat *)
(* = noRepeats_length_lemma (S.seq_to_list p)  ; n - length p *)
let non_visited_nodes (#n:nat) (g:graph0 n) (p:path g{elementary p}) : nat
= assume (n > length p)  ; n - length p

(* TODO : the basic structure of this lemma is set up but it still needs to be proven *)
#set-options "--detail_errors"
let rec extremal_node_or_cycle_from_aux (#n:nat) (g:graph0 n) (p:path g{elementary p})
  : Pure (either (_in g) (path g))
    (requires True)
    (ensures (fun r -> match r with | Inl i -> g @^ i == [] | Inr p' -> elementary_cycle p'))
    (decreases (non_visited_nodes g p))
=
  match g @^ (to p) with
  | [] -> Inl (to p)
  | i :: _ ->
    index_of_l_spec (fun j -> j = i) p ;
    match index_of_l (fun j -> j = i) p with
    | None ->
      assume (elementary (p `snoc` i)) ;
      extremal_node_or_cycle_from_aux #n g (p `snoc` i)
    | Some i0 ->
      admit () ;
      assert (p @^ i0 == i) ;
      let p' : path g = S.slice p i0 (length p) in
      let p'' : path g = p' `snoc` i in
      assert (p' @^ 0 == i) ;
      assume (elementary p') ;
      S.lemma_eq_elim (S.slice p'' 0 (length p'' - 1)) p' ;
      assert (elementary p'') ;
      assert (from p'' == i /\ to p'' == i) ;
      Inr  p''

let extremal_node_or_cycle_from
  (#n:nat)
  (g:graph0 n)
  (i0:_in g)
  : either (i:_in g{g @^ i == []}) (p:path g{elementary_cycle p})
= match extremal_node_or_cycle_from_aux #n g (empty_path_at g i0) with
  | Inl i -> Inl i
  | Inr p -> Inr p


let rec disconnected (#n:nat) (g:graph0 n)
  : Lemma (requires (connected g /\ edge_size g < n - 1)) (ensures False)
    (decreases (node_size g + edge_size g))
= if edge_size g = 0 then
    (* There is no path between (g @^ 0) and (g @^ 1) *)
    admit ()
  else
    match extremal_node_or_cycle_from g 0 with
    | Inl i ->
      let g' : graph0 (n-1) =
        (* Removing node i preserves connectedness *)
        admit ()
      in
      disconnected g'
   | Inr p ->
     let g' : graph0 n =
       (* Removing an edge in an elementary_cycle preserves connectedness *)
       admit ()
     in
     disconnected g'

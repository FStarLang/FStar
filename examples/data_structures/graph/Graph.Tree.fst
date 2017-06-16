module Graph.Tree

open Graph.Base
open Seq.Complements

module S = FStar.Seq
module L = FStar.List.Tot

let connected (#n:nat) (g:graph0 n) =
  forall (i j:_in g). exists (p:path g). from p == i /\ to p == j


(* TODO : the basic structure of this lemma is set up but it still needs to be proven *)
let rec extremal_node_or_cycle_from_aux (#n:nat) (g:graph0 n) (p:path g)
  : Pure (either (_in g) (path g))
    (requires (elementary p))
    (ensures (fun r -> match r with | Inl i -> g @^ i == [] | Inr p' -> elementary_cycle p'))
    (decreases (n - length p))
= (* TODO : Remove me !!! *) admit () ;
  match g @^ (to p) with
  | [] -> Inl (to p)
  | i :: _ ->
    match S.seq_find (fun j -> j = i) p with
    | None -> extremal_node_or_cycle_from_aux #n g (p `snoc` i)
    | Some i0 ->
      Inr (S.slice p i0 (length p) `snoc` i)

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

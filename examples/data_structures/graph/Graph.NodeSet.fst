module Graph.NodeSet

module L = FStar.List.Tot
open FStar.Fin
open Seq.Complements
module C = FStar.Classical
open Graph.Base
open List.Complements

let _in (l:list 'a) = k:nat{k < L.length l}
let ( @^ ) (l:list 'a) (i:_in l) : 'a = L.index l i

let disjoint (#n:nat) (n1: list (fin n)) (n2:list (fin n)) = forall x . L.mem x n1 ==> not (L.mem x  n2)


(* Not the same as union! *)
let append (#n:nat)(n1 n2:nodeset n )
 : Pure (nodeset n)
 (requires (disjoint n1 n2))
 (ensures (fun p' -> True))
 =
 L.noRepeats_append_intro (n1) (n2);
 L.append n1 n2

let lemma_disjoint_append (#n:nat) (n1 n2 n3: nodeset n)
  : Lemma (requires (disjoint n1 n2) /\ (disjoint n1 n3) /\ (disjoint n2 n3))
    (ensures (disjoint n1 n2 /\ disjoint (append n1 n2) n3))
=   L.append_mem_forall n1 n2

let rec list_to_nodeset_aux (#n:nat) (l:list (fin n)) (n' : nodeset n)
 : Pure (nodeset n) (requires (disjoint l n')) (ensures (fun p -> True))
 = match l with
 | [] -> n'
 | hd :: tl -> if L.mem hd tl then list_to_nodeset_aux tl n' 
   else list_to_nodeset_aux tl (hd :: n')

let list_to_nodeset (#n:nat) (l:list (fin n)) = list_to_nodeset_aux l []


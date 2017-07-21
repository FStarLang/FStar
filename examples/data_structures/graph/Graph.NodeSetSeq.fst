module Graph.NodeSetSeq

open FStar.Fin
module SC = Seq.Complements
module C = FStar.Classical
open Graph.Base
module S = FStar.Seq
module E = Graph.Elementary

let _in (s:S.seq 'a) = SC._in s
let ( @^ ) (s:S.seq 'a) (i:_in s) : 'a = S.index s i

let disjoint = SC.disjoint

(* Not the same as union! *)
let append (#n:nat)(n1 n2:nodesetseq n )
 : Pure (nodesetseq n)
 (requires (disjoint n1 n2))
 (ensures (fun p' -> True))
 =
 E.lemma_mutually_exclusive_elementary_append n1 n2;
 S.append n1 n2

let lemma_disjoint_append (#n:nat) (n1 n2 n3: nodesetseq n)
  : Lemma (requires (disjoint n1 n2) /\ (disjoint n1 n3) /\ (disjoint n2 n3))
    (ensures (disjoint n1 n2 /\ disjoint (append n1 n2) n3))
=   SC.lemma_disjoint_append n1 n2 n3

let rec seq_to_nodesetseq_aux (#n:nat) (s:S.seq (fin n)) (n' : nodesetseq n)
 : Pure (nodesetseq n) (requires (disjoint s n')) (ensures (fun p -> True)) (decreases (S.length s))
 = match S.length s with
 | 0 -> n'
 | x -> let hd = S.head s in let tl = S.tail s in let hds = S.slice s 0 1 in
   SC.lemma_disjoint_slice n' s 1 (S.length s); SC.lemma_disjoint_slice n' s 0 1;
   let n'' = append hds n' in
   if S.mem hd tl then seq_to_nodesetseq_aux tl n' 
    else
    (
     SC.lemma_disjoint_append hds n' tl;
     seq_to_nodesetseq_aux tl n''
    )

let seq_list_to_nodesetseq (#n:nat) (s:S.seq (fin n)) = seq_to_nodesetseq_aux s S.createEmpty

module Set.Complements

open FStar.Classical
open FStar.Set
open List.Complements
module L = FStar.List.Tot

let empty_set_union (#a:eqtype) (s:set a)
 : Lemma (requires (True)) (ensures (union empty s == s))
 = lemma_equal_intro s (union empty s)

let rec as_set_mem_in_forall (#a:eqtype) (l:list a)
 : Lemma (requires (True))
   (ensures (forall (x:a). L.mem x l <==>  mem x (as_set l)))
  = match l with
  | [] -> ()
  | hd :: tl -> as_set_mem_in_forall tl
  

let as_set_mem_equiv (#a:eqtype) (l1 l2:list a)
 : Lemma (requires (forall (x:a). L.mem x l1 = L.mem x l2))
   (ensures (as_set l1) == (as_set l2))
   = as_set_mem_in_forall l1; as_set_mem_in_forall l2;
     lemma_equal_intro (as_set l1) (as_set l2)

let union_equiv (#a:eqtype) (s1 s2 s3:set a)
 : Lemma (requires (forall (x:a) . (mem x s1 || mem x s2) = mem x s3))
   (ensures (union s1 s2) == s3)
   = lemma_equal_intro (union s1 s2) s3

let as_set_union_equiv (#a:eqtype) (l1 l2 l3: list a)
: Lemma (requires (forall (x:a) . (L.mem x l1 || L.mem x l2) = L.mem x l3))
   (ensures (union (as_set l1) (as_set l2)) == as_set l3)
   = as_set_mem_in_forall l1; as_set_mem_in_forall l2;
     as_set_mem_in_forall l3;
     union_equiv (as_set l1) (as_set l2) (as_set l3)

let rec as_set_append (#a:eqtype) (l1 l2:list a)
 : Lemma (requires (True)) 
   (ensures (as_set (L.append l1 l2)) == (union (as_set l1) (as_set l2)))
  (decreases (L.length l2))
   = L.append_mem_forall l1 l2; as_set_union_equiv l1 l2 (L.append l1 l2)

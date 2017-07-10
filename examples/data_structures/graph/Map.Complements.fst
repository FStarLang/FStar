module Map.Complements

open FStar.Classical
open FStar.Map
module S = FStar.Set
open List.Complements
module L = FStar.List.Tot
module SC = Set.Complements

let lemma_SelUpd2_forall (#key:eqtype) ( #value:Type) (m: t key value) (k:key) (v:value)
 : Lemma (requires True) (ensures (forall (x:key) . x =!= k ==>  sel (upd m k v) x == sel m x ))
  = ()
   
   
let has_domain_upd (#key:eqtype) ( #value:Type) (m: t key value) (k:key) (v:value)
 : Lemma (requires (True)) (ensures has_dom (upd m k v) (S.union (domain m) (S.singleton k)))
 = ()



let rec domain_lemma_aux (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key)
 (fv: key -> value) (pre:list key) (post:list key) (m':t key value)
 : Lemma (requires m' == L.fold_left (fun acc i -> upd acc i (fv i)) m pre /\ L.append pre post == l1
   /\ has_dom m' (S.union (domain m) (S.as_set pre)))
   (ensures (has_dom (L.fold_left (fun acc i -> upd acc i (fv i)) m l1)
    (S.union (domain m) (S.as_set l1))))
    (decreases (L.length post))
    = match post with
    | [] -> L.append_l_nil pre
    | hd :: tl ->
      let pre' = L.append pre [hd] in
      let post' = tl in
      let m'' = upd m' hd (fv hd) in
      SC.as_set_append pre [hd];
      L.append_l_cons hd tl pre;
      L.fold_left_append (fun acc i -> upd acc i (fv i)) pre [hd];
      domain_lemma_aux m l1 fv pre' post' m''

let domain_lemma (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key) (fv:key->value)
 : Lemma (requires (True))
   (ensures (has_dom (L.fold_left (fun acc i -> upd acc i (fv i)) m l1)
   (S.union (domain m) (S.as_set l1))))
   =    
   domain_lemma_aux m l1 fv [] l1 m

let rec lemma_fold_upd1_aux (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key)
 (fv: key -> value) (pre:list key) (post:list key) (m':t key value)
 : Lemma (requires m' == L.fold_left (fun acc i -> upd acc i (fv i)) m pre /\ L.append pre post == l1
   /\ (forall (x:key). L.mem x pre = false ==>  sel m x == sel m' x))
   (ensures (forall (x:key). L.mem x l1 = false ==>  
   sel m x == sel (L.fold_left (fun acc i -> upd acc i (fv i)) m l1) x))
    (decreases (L.length post))
    = match post with
    | [] -> L.append_l_nil pre
    | hd :: tl -> 
      let pre' = L.append pre [hd] in
      let post' = tl in
      let m'' = upd m' hd (fv hd) in
      L.append_l_cons hd tl pre;
      L.fold_left_append (fun acc i -> upd acc i (fv i)) pre [hd];
      L.append_mem_forall pre [hd];  
      lemma_fold_upd1_aux m l1 fv pre' post' m''

let lemma_fold_upd1 (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key) (fv:key->value)
 : Lemma (requires (True))
   (ensures (forall (x:key). L.mem x l1 = false ==>  
   sel m x == sel (L.fold_left (fun acc i -> upd acc i (fv i)) m l1) x))
   
   =    
   lemma_fold_upd1_aux m l1 fv [] l1 m


let rec lemma_fold_upd2_aux (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key)
 (fv: key -> value) (pre:list key) (post:list key) (m':t key value)
 : Lemma (requires m' == L.fold_left (fun acc i -> upd acc i (fv i)) m pre /\ L.append pre post == l1
   /\ (forall (x:key). L.mem x pre = true ==>  (fv x) == sel m' x))
   (ensures (forall (x:key). L.mem x l1 = true ==>  
   (fv x) == sel (L.fold_left (fun acc i -> upd acc i (fv i)) m l1) x))
    (decreases (L.length post))
    = match post with
    | [] -> L.append_l_nil pre
    | hd :: tl -> 
      let pre' = L.append pre [hd] in
      let post' = tl in
      let m'' = upd m' hd (fv hd) in
      L.append_l_cons hd tl pre;
      L.fold_left_append (fun acc i -> upd acc i (fv i)) pre [hd];
      L.append_mem_forall pre [hd];  
      lemma_fold_upd2_aux m l1 fv pre' post' m''

let lemma_fold_upd2 (#key:eqtype) ( #value:Type) (m: t key value) (l1:list key) (fv:key->value)
 : Lemma (requires (True))
   (ensures (forall (x:key). L.mem x l1 = true ==>  
   (fv x) == sel (L.fold_left (fun acc i -> upd acc i (fv i)) m l1) x))
   
   =    
   lemma_fold_upd2_aux m l1 fv [] l1 m

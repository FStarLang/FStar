module CBOR.Spec.Map
include CBOR.Spec.Type

let rec list_for_all_weaken
  (#t: Type)
  (p1: t -> bool)
  (p2: t -> bool { forall x . p1 x ==> p2 x })
  (l: list t)
: Lemma
  (requires (List.Tot.for_all p1 l))
  (ensures (List.Tot.for_all p2 l))
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_weaken p1 p2 q

let rec list_sorted_cons_elim
  (#t1: Type)
  (key_order: t1 -> t1 -> bool {
    forall x y z . (key_order x y /\ key_order y z) ==> key_order x z
  })
  (a: t1)
  (q: list t1)
: Lemma
  (requires (List.Tot.sorted key_order (a :: q)))
  (ensures (List.Tot.for_all (key_order a) q))
  (decreases q)
= match q with
  | [] -> ()
  | b :: r ->
    list_sorted_cons_elim key_order b r;
    list_for_all_weaken (key_order b) (key_order a) r

let rec list_sorted_map_entry_order_lt_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
  (k: t1)
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l) /\ List.Tot.memP k (List.Tot.map fst l)))
  (ensures (key_order (fst a) k))
  (decreases l)
= let b :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == fst b)
  then ()
  else list_sorted_map_entry_order_lt_tail key_order b q k

let list_sorted_map_entry_order_not_memP_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l)))
  (ensures (~ (List.Tot.memP (fst a) (List.Tot.map fst l))))
= Classical.move_requires (list_sorted_map_entry_order_lt_tail key_order a l) (fst a)

let rec list_sorted_map_entry_order_no_repeats
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
= match l with
  | [] -> ()
  | a :: q ->
    list_sorted_map_entry_order_no_repeats key_order q;
    list_sorted_map_entry_order_not_memP_tail key_order a q


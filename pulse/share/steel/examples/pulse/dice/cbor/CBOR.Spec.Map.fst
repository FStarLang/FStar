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

let rec list_tot_for_all_order_trans
    (#t1: Type)
    (order: t1 -> t1 -> bool {
      (forall x . order x x == false) /\
      (forall x y z . (order x y /\ order y z) ==> order x z)
    })
    (k1v1: _)
    (k2v2: _)
    (l1: list t1)
  : Lemma
  (requires (order k1v1 k2v2 /\
    List.Tot.for_all (order k2v2) l1
  ))
  (ensures (
    List.Tot.for_all (order k1v1) l1
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_tot_for_all_order_trans order k1v1 k2v2 q

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

let rec list_ghost_assoc_append
    (#tk #tv: Type)
    (k: tk)
    (l1 l2: list (tk & tv))
: Lemma
    (ensures (list_ghost_assoc k (l1 `List.Tot.append` l2) == (
        match list_ghost_assoc k l1 with
        | Some v -> Some v
        | None -> list_ghost_assoc k l2
    )))
    (decreases l1)
= match l1 with
| [] -> ()
| (k1, _ ) :: q1 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k1)
    then ()
    else list_ghost_assoc_append k q1 l2

let rec list_ghost_assoc_mem_intro
  (#tk #tv: Type)
  (k: tk)
  (v: tv)
  (l: list (tk & tv))
: Lemma
  (requires (list_ghost_assoc k l == Some v))
  (ensures (List.Tot.memP (k, v) l))
  (decreases l)
= let (k', v') :: l' = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
  then ()
  else list_ghost_assoc_mem_intro k v l'

let rec list_ghost_assoc_no_repeats_mem_elim
  (#tk #tv: Type)
  (k: tk)
  (v: tv)
  (l: list (tk & tv))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l) /\
    List.Tot.memP (k, v) l
  ))
  (ensures (list_ghost_assoc k l == Some v))
  (decreases l)
= List.Tot.memP_map_intro fst (k, v) l;
  let (k', v') :: l' = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
  then
    if FStar.StrongExcludedMiddle.strong_excluded_middle (v == v')
    then ()
    else List.Tot.memP_map_intro fst (k, v) l'
  else list_ghost_assoc_no_repeats_mem_elim k v l'

let list_ghost_assoc_no_repeats_mem
  (#tk #tv: Type)
  (l: list (tk & tv))
  (k: tk)
  (v: tv)
: Lemma
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l) ==> (list_ghost_assoc k l == Some v <==> List.Tot.memP (k, v) l)))
= Classical.move_requires (list_ghost_assoc_no_repeats_mem_elim k v) l;
  Classical.move_requires (list_ghost_assoc_mem_intro k v) l

let list_ghost_assoc_no_repeats_equiv'
  (#tk #tv: Type)
  (l1 l2: list (tk & tv))
  (k: tk)
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    (forall kv . List.Tot.memP kv l1 <==> List.Tot.memP kv l2)
  ))
  (ensures (list_ghost_assoc k l1 == list_ghost_assoc k l2))
= match list_ghost_assoc k l1 with
  | None ->
    begin match list_ghost_assoc k l2 with
    | None -> ()
    | Some v ->
      list_ghost_assoc_no_repeats_mem l2 k v;
      list_ghost_assoc_no_repeats_mem l1 k v
    end
  | Some v ->
    list_ghost_assoc_no_repeats_mem l1 k v;
    list_ghost_assoc_no_repeats_mem l2 k v

let list_ghost_assoc_no_repeats_equiv
  (#tk #tv: Type)
  (l1 l2: list (tk & tv))
: Lemma
  (requires (
    List.Tot.no_repeats_p (List.Tot.map fst l1) /\
    List.Tot.no_repeats_p (List.Tot.map fst l2) /\
    (forall kv . List.Tot.memP kv l1 <==> List.Tot.memP kv l2)
  ))
  (ensures (forall k . list_ghost_assoc k l1 == list_ghost_assoc k l2))
= Classical.forall_intro (Classical.move_requires (list_ghost_assoc_no_repeats_equiv' l1 l2))

[@@noextract_to "krml"] noextract
let rec map_sort_merge
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (accu: list (t1 & t2))
  (l1: list (t1 & t2))
  (l2: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  |  (k1, v1) :: l1', (k2, v2) :: l2' ->
    begin let c = key_compare k1 k2 in
      if c = 0
      then (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
      else if c < 0
      then map_sort_merge key_compare (accu `List.Tot.append` [(k1, v1)]) l1' l2
      else
        map_sort_merge key_compare (accu `List.Tot.append` [(k2, v2)]) l1 l2'
        // TODO in this case:
        // 1. prove that the sort is stable, i.e. that the maps are extensionally equal throughout
        // 2. extract and swap the whole prefix of l2 less than the head of l1, rather than just the head of l2
     end
  | [], _ -> (true, accu `List.Tot.append` l2)
  | _, [] -> (true, accu `List.Tot.append` l1)

let rec list_sorted_append_elim
  (#t: Type)
  (order: t -> t -> bool)
  (l1 l2: list t)
: Lemma
  (requires (List.Tot.sorted order (l1 `List.Tot.append` l2)))
  (ensures (
    List.Tot.sorted order l1 /\
    List.Tot.sorted order l2
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | [_] -> ()
  | a :: b :: q ->
    list_sorted_append_elim order (b :: q) l2

let rec list_sorted_append_chunk_intro
  (#t: Type)
  (order: t -> t -> bool)
  (l1 l2 l3: list t)
: Lemma
  (requires (
    List.Tot.sorted order (l1 `List.Tot.append` l2) /\
    List.Tot.sorted order (l2 `List.Tot.append` l3) /\
    Cons? l2
  ))
  (ensures (
    List.Tot.sorted order (l1 `List.Tot.append` (l2 `List.Tot.append` l3))
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | [a] -> () // because of List.Tot.sorted (l2 `List.Tot.append` l3) and Cons? l2
  | a :: l1' -> list_sorted_append_chunk_intro order l1' l2 l3

let rec list_sorted_order_elim
  (#t: Type)
  (order: t -> t -> bool)
  (l0: list t)
  (a1: t)
  (l1: list t)
  (a2: t)
  (l2: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    List.Tot.sorted order (l0 `List.Tot.append` (a1 :: (l1 `List.Tot.append` (a2 :: l2))))
  ))
  (ensures (order a1 a2 == true))
  (decreases (List.Tot.length l0 + List.Tot.length l1))
= match l0 with
  | [] ->
    begin match l1 with
    | [] -> ()
    | a1' :: l1' ->
      list_sorted_order_elim order [] a1' l1' a2 l2 // and transitivity
    end
  | a0 :: l0' ->
    list_sorted_order_elim order l0' a1 l1 a2 l2

let rec list_sorted_append_chunk_elim
  (#t: Type)
  (order: t -> t -> bool)
  (l1 l2 l3: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    List.Tot.sorted order (l1 `List.Tot.append` (l2 `List.Tot.append` l3))
  ))
  (ensures (
    List.Tot.sorted order (l1 `List.Tot.append` l3)
  ))
  (decreases l1)
= match l1 with
  | [] -> list_sorted_append_elim order l2 l3
  | [a] ->
    begin match l3 with
    | [] -> ()
    | b :: q ->
      list_sorted_append_elim order l2 l3;
      list_sorted_order_elim order [] a l2 b q
    end
  | _ :: l1' -> list_sorted_append_chunk_elim order l1' l2 l3

let rec map_sort_merge_correct
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (accu: list (t1 & t2))
  (l1: list (t1 & t2))
  (l2: list (t1 & t2))
: Lemma
  (requires (
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z) /\
    (forall x y . key_order x y == (key_compare x y < 0)) /\
    (forall x y . key_compare x y == 0 <==> x == y) /\
    (forall x y . (key_compare x y < 0 <==> key_compare y x > 0)) /\
    List.Tot.sorted (map_entry_order key_order _) (accu `List.Tot.append` l1) /\
    List.Tot.sorted (map_entry_order key_order _) (accu `List.Tot.append` l2)
  ))
  (ensures (
    let (sorted, res) = map_sort_merge key_compare accu l1 l2 in
    (forall x . List.Tot.memP x res <==> List.Tot.memP x (accu `List.Tot.append` (l1 `List.Tot.append` l2))) /\
    (List.Tot.no_repeats_p (List.Tot.map fst res) <==> List.Tot.no_repeats_p (List.Tot.map fst (accu `List.Tot.append` (l1 `List.Tot.append` l2)))) /\
    (if sorted
    then List.Tot.sorted (map_entry_order key_order _) res
    else ~ (List.Tot.no_repeats_p (List.Tot.map fst res))
    )
  ))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  | [], _ -> ()
  | _, [] -> List.Tot.append_l_nil l1
  | (k1, v1) :: l1', (k2, v2) :: l2' ->
    List.Tot.map_append fst l1 l2;
    List.Tot.map_append fst accu (l1 `List.Tot.append` l2);
    let c = key_compare k1 k2 in
    if c = 0
    then
      List.Tot.no_repeats_p_false_intro (List.Tot.map fst accu) [k1] (List.Tot.map fst l1') (List.Tot.map fst l2')
    else if c < 0
    then begin
      let accu' = accu `List.Tot.append` [(k1, v1)] in
      List.Tot.append_assoc accu l1 l2;
      List.Tot.append_assoc accu [(k1, v1)] l1';
      List.Tot.append_assoc accu' l1' l2;
      List.Tot.append_assoc accu [(k1, v1)] l2;
      list_sorted_append_elim (map_entry_order key_order _) accu' l1';
      list_sorted_append_elim (map_entry_order key_order _) accu l2;
      list_sorted_append_chunk_intro (map_entry_order key_order _) accu [(k1, v1)] l2;
      map_sort_merge_correct key_order key_compare accu' l1' l2
    end
    else begin
      let accu' = accu `List.Tot.append` [(k2, v2)] in
      List.Tot.append_memP_forall l1 l2;
      List.Tot.append_memP_forall accu (l1 `List.Tot.append` l2);
      List.Tot.append_memP_forall accu [(k2, v2)];
      List.Tot.append_memP_forall l1 l2';
      List.Tot.append_memP_forall accu' (l1 `List.Tot.append` l2');
      List.Tot.no_repeats_p_append_permut (List.Tot.map fst accu) [k2] (List.Tot.map fst l1) [] (List.Tot.map fst l2');
      List.Tot.append_assoc (List.Tot.map fst accu) [k2] (List.Tot.map fst l1 `List.Tot.append` List.Tot.map fst l2');
      List.Tot.map_append fst accu [(k2, v2)];
      List.Tot.map_append fst l1 l2';
      List.Tot.map_append fst accu' (l1 `List.Tot.append` l2');
      List.Tot.append_assoc accu [(k2, v2)] l2';
      list_sorted_append_elim (map_entry_order key_order _) accu' l2';
      list_sorted_append_elim (map_entry_order key_order _) accu l1;
      list_sorted_append_chunk_intro (map_entry_order key_order _) accu [(k2, v2)] l1;
      List.Tot.append_assoc accu [(k2, v2)] l1;
      map_sort_merge_correct key_order key_compare accu' l1 l2'
    end

let rec list_splitAt_length
  (#t: Type)
  (n: nat)
  (l: list t)
: Lemma
  (requires (List.Tot.length l >= n))
  (ensures (
    let (l1, l2) = List.Tot.splitAt n l in
    List.Tot.length l1 == n /\
    List.Tot.length l1 + List.Tot.length l2 == List.Tot.length l
  ))
  [SMTPat (List.Tot.splitAt n l)]
= if n = 0 then () else list_splitAt_length (n - 1) (List.Tot.tl l)

let rec list_splitAt_append
  (#t: Type)
  (n: nat)
  (l: list t)
: Lemma
  (ensures (let (l1, l2) = List.Tot.splitAt n l in
    l == l1 `List.Tot.append` l2
  ))
  [SMTPat (List.Tot.splitAt n l)]
= match l with
  | [] -> ()
  | a :: q ->
    if n = 0 then () else list_splitAt_append (n - 1) q

[@@noextract_to "krml"] noextract
let rec map_sort
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then (true, l)
  else
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    let (res, l1') = map_sort key_compare l1 in
    if not res
    then (false, l1' `List.Tot.append` l2)
    else
      let (res, l2') = map_sort key_compare l2 in
      if not res
      then (false, l1' `List.Tot.append` l2')
      else map_sort_merge key_compare [] l1' l2'

let list_memP_map_forall
  (#t1 #t2: Type)
  (f: t1 -> t2)
  (l: list t1)
: Lemma
  (forall y . List.Tot.memP y (List.Tot.map f l) <==> (exists x . List.Tot.memP x l /\ y == f x))
= Classical.forall_intro (fun y -> List.Tot.memP_map_elim f y l);
  Classical.forall_intro (fun x -> List.Tot.memP_map_intro f x l)

#push-options "--z3rlimit 16"

#restart-solver
let rec map_sort_correct
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Lemma
  (requires (
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z) /\
    (forall x y . key_order x y == (key_compare x y < 0)) /\
    (forall x y . key_compare x y == 0 <==> x == y) /\
    (forall x y . (key_compare x y < 0 <==> key_compare y x > 0))
  ))
  (ensures (let (res, l') = map_sort key_compare l in
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true <==> List.Tot.no_repeats_p (List.Tot.map fst l)) /\
    (res == true ==> (
      List.Tot.sorted (map_entry_order key_order _) l' /\
      (forall k . list_ghost_assoc k l' == list_ghost_assoc k l)
    ))
  ))
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then ()
  else begin
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    List.Tot.append_memP_forall l1 l2;
    List.Tot.map_append fst l1 l2;
    List.Tot.no_repeats_p_append (List.Tot.map fst l1) (List.Tot.map fst l2);
    List.Tot.append_memP_forall (List.Tot.map fst l1) (List.Tot.map fst l2);
    list_memP_map_forall fst l1;
    list_memP_map_forall fst l2;
    let (res, l1') = map_sort key_compare l1 in
    map_sort_correct key_order key_compare l1;
    list_memP_map_forall fst l1';
    List.Tot.append_memP_forall (List.Tot.map fst l1') (List.Tot.map fst l2);
    List.Tot.no_repeats_p_append (List.Tot.map fst l1') (List.Tot.map fst l2);
    List.Tot.map_append fst l1' l2;
    List.Tot.append_memP_forall l1' l2;
    if not res
    then ()
    else begin
      let (res, l2') = map_sort key_compare l2 in
      map_sort_correct key_order key_compare l2;
      list_memP_map_forall fst l2';
      List.Tot.append_memP_forall (List.Tot.map fst l1') (List.Tot.map fst l2');
      List.Tot.no_repeats_p_append (List.Tot.map fst l1') (List.Tot.map fst l2');
      List.Tot.map_append fst l1' l2';
      List.Tot.append_memP_forall l1' l2';
      if not res
      then ()
      else begin
        let (res, l') = map_sort_merge key_compare [] l1' l2' in
        assert (map_sort key_compare l == (res, l'));
        map_sort_merge_correct key_order key_compare [] l1' l2';
        assert (forall x . List.Tot.memP x l' <==> (List.Tot.memP x l1' \/ List.Tot.memP x l2'));
        assert (forall x . List.Tot.memP x l' <==> List.Tot.memP x l);
        assert (List.Tot.no_repeats_p (List.Tot.map fst l') <==> List.Tot.no_repeats_p (List.Tot.map fst l));
        if res
        then begin
          assert (List.Tot.sorted (map_entry_order key_order _) l');
          list_sorted_map_entry_order_no_repeats key_order l';
          list_ghost_assoc_no_repeats_equiv l l';
          assert (forall k . list_ghost_assoc k l' == list_ghost_assoc k l)
        end
        else ()
      end
    end
  end

  #pop-options

module Pulse.Lib.Sort.Merge.Spec
open Pulse.Lib.Pervasives

[@@noextract_to "krml"] noextract
let rec spec_merge
  (#t: Type)
  (compare: t -> t -> int)
  (accu: list t)
  (l1: list t)
  (l2: list t)
: Tot (bool & list t)
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  |  x1 :: l1', x2 :: l2' ->
    begin let c = compare x1 x2 in
      if c = 0
      then (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
      else if c < 0
      then spec_merge compare (accu `List.Tot.append` [x1]) l1' l2
      else
        spec_merge compare (accu `List.Tot.append` [x2]) l1 l2'
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

let rec list_index_append_r
  (#t: Type)
  (l1 l2: list t)
  (i: nat)
: Lemma
  (requires i < List.Tot.length l2)
  (ensures List.Tot.length (List.Tot.append l1 l2) == List.Tot.length l1 + List.Tot.length l2 /\
    List.Tot.index (List.Tot.append l1 l2) (List.Tot.length l1 + i) == List.Tot.index l2 i
  )
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_index_append_r q l2 i

#push-options "--z3rlimit 16"

#restart-solver
let rec spec_merge_correct
  (#t: Type)
  (order: t -> t -> bool)
  (compare: t -> t -> int)
  (accu: list t)
  (l1: list t)
  (l2: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0)) /\
    List.Tot.sorted order (accu `List.Tot.append` l1) /\
    List.Tot.sorted order (accu `List.Tot.append` l2)
  ))
  (ensures (
    let (sorted, res) = spec_merge compare accu l1 l2 in
    List.Tot.length res == List.Tot.length accu + List.Tot.length l1 + List.Tot.length l2 /\
    (forall x . List.Tot.memP x res <==> List.Tot.memP x (accu `List.Tot.append` (l1 `List.Tot.append` l2))) /\
    (if sorted
    then List.Tot.sorted order res
    else exists x1 x2 . (List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
    )
  ))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  | [], _ -> List.Tot.append_length accu l2
  | _, [] -> List.Tot.append_l_nil l1; List.Tot.append_length accu l1
  | x1 :: l1', x2 :: l2' ->
    let c = compare x1 x2 in
    if c = 0
    then begin
      List.Tot.append_length l1 l2;
      List.Tot.append_length accu (List.Tot.append l1 l2)
    end
    else if c < 0
    then begin
      let accu' = accu `List.Tot.append` [x1] in
      List.Tot.append_length accu [x1];
      List.Tot.append_assoc accu l1 l2;
      List.Tot.append_assoc accu [x1] l1';
      List.Tot.append_assoc accu' l1' l2;
      List.Tot.append_assoc accu [x1] l2;
      list_sorted_append_elim order accu' l1';
      list_sorted_append_elim order accu l2;
      list_sorted_append_chunk_intro order accu [x1] l2;
      spec_merge_correct order compare accu' l1' l2
    end
    else begin
      let accu' = accu `List.Tot.append` [x2] in
      List.Tot.append_length accu [x2];
      List.Tot.append_memP_forall l1 l2;
      List.Tot.append_memP_forall accu (l1 `List.Tot.append` l2);
      List.Tot.append_memP_forall accu [x2];
      List.Tot.append_memP_forall l1 l2';
      List.Tot.append_memP_forall accu' (l1 `List.Tot.append` l2');
      List.Tot.append_assoc accu [x2] l2';
      list_sorted_append_elim order accu' l2';
      list_sorted_append_elim order accu l1;
      list_sorted_append_chunk_intro order accu [x2] l1;
      List.Tot.append_assoc accu [x2] l1;
      spec_merge_correct order compare accu' l1 l2'
    end

#pop-options

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
let rec spec_sort
  (#t: Type)
  (compare: t -> t -> int)
  (l: list t)
: Tot (bool & list t)
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then (true, l)
  else
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    let _ = list_splitAt_length (len / 2) l in
    let _ = assert (List.Tot.length l1 == len / 2) in
    let (res, l1') = spec_sort compare l1 in
    if not res
    then (false, l1' `List.Tot.append` l2)
    else
      let (res, l2') = spec_sort compare l2 in
      if not res
      then (false, l1' `List.Tot.append` l2')
      else spec_merge compare [] l1' l2'

let exists4_elim
  (#t1 #t2 #t3 #t4: Type)
  (p: t1 -> t2 -> t3 -> t4 -> prop)
  (q: prop)
  (prf: (x1: t1) -> (x2: t2) -> (x3: t3) -> (x4: t4) -> Lemma
    (requires p x1 x2 x3 x4)
    (ensures q)
  )
: Lemma
  (requires exists x1 x2 x3 x4 . p x1 x2 x3 x4)
  (ensures q)
= Classical.forall_intro_4 (fun x1 x2 x3 x4 -> Classical.move_requires (prf x1 x2 x3) x4)

#push-options "--split_queries always"

#restart-solver
let rec spec_sort_correct
  (#t: Type)
  (order: t -> t -> bool)
  (compare: t -> t -> int)
  (l: list t)
: Lemma
  (requires (
    (forall x y z . (order x y /\ order y z) ==> order x z) /\
    (forall x y . order x y == (compare x y < 0)) /\
    (forall x y . (compare x y < 0 <==> compare y x > 0))
  ))
  (ensures (let q = spec_sort compare l in
    let res : bool = fst q in
    let l'  = snd q in
    List.Tot.length l' == List.Tot.length l /\
    (forall x . List.Tot.memP x l' <==> List.Tot.memP x l) /\
    (if res then
      List.Tot.sorted order l'
    else exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0
    ))
  )
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then ()
  else begin
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    list_splitAt_append (len / 2) l;
    List.Tot.append_length l1 l2;
    List.Tot.append_memP_forall l1 l2;
    let (res, l1') = spec_sort compare l1 in
    spec_sort_correct order compare l1;
    List.Tot.append_memP_forall l1' l2;
    if not res
    then begin
      let prf
        (l1_1 l1_2: list t)
        (x1 x2: t)
      : Lemma
        (requires (l1 == List.Tot.append l1_1 l1_2 /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 l1_2 /\ compare x1 x2 == 0))
        (ensures (l == List.Tot.append l1_1 (List.Tot.append l1_2 l2) /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 (List.Tot.append l1_2 l2) /\ compare x1 x2 == 0))
      = List.Tot.append_assoc l1_1 l1_2 l2;
        List.Tot.append_memP_forall l1_2 l2
      in
      exists4_elim (fun l1_1 l1_2 x1 x2 -> l1 == List.Tot.append l1_1 l1_2 /\ List.Tot.memP x1 l1_1 /\ List.Tot.memP x2 l1_2 /\ compare x1 x2 == 0)
        (exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
        (fun l1_1 l1_2 x1 x2 -> prf l1_1 l1_2 x1 x2);
      List.Tot.append_length l1' l2
    end
    else begin
      let (res, l2') = spec_sort compare l2 in
      spec_sort_correct order compare l2;
      List.Tot.append_memP_forall l1' l2';
      if not res
      then begin
        let prf
          (l2_1 l2_2: list t)
          (x1 x2: t)
        : Lemma
          (requires (l2 == List.Tot.append l2_1 l2_2 /\ List.Tot.memP x1 l2_1 /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0))
          (ensures (l == List.Tot.append (List.Tot.append l1 l2_1) l2_2 /\ List.Tot.memP x1 (List.Tot.append l1 l2_1) /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0))
        = List.Tot.append_assoc l1 l2_1 l2_2;
          List.Tot.append_memP_forall l1 l2_1
        in
        exists4_elim (fun l2_1 l2_2 x1 x2 ->  l2 == List.Tot.append l2_1 l2_2 /\ List.Tot.memP x1 l2_1 /\ List.Tot.memP x2 l2_2 /\ compare x1 x2 == 0)
          (exists l1 l2 x1 x2 . l == List.Tot.append l1 l2 /\ List.Tot.memP x1 l1 /\ List.Tot.memP x2 l2 /\ compare x1 x2 == 0)
          (fun l1_1 l1_2 x1 x2 -> prf l1_1 l1_2 x1 x2);
        List.Tot.append_length l1' l2'
      end
      else begin
        let (res, l') = spec_merge compare [] l1' l2' in
        assert (spec_sort compare l == (res, l'));
        spec_merge_correct order compare [] l1' l2';
        assert (forall x . List.Tot.memP x l' <==> (List.Tot.memP x l1' \/ List.Tot.memP x l2'));
        assert (forall x . List.Tot.memP x l' <==> List.Tot.memP x l);
        if res
        then begin
          assert (List.Tot.sorted order l')
        end
        else ()
      end
    end
  end

#pop-options

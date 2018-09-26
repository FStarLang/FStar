module FStar.List.Pure.Properties

open FStar.List.Tot.Base
open FStar.List.Pure.Base
open FStar.List.Tot.Properties

(** Properties of splitAt *)

let rec splitAt_length
  (#a:Type)
  (n:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l_1, l_2 = splitAt n l in
      if length l < n then
        length l_1 == length l /\ length l_2 == 0
      else
        length l_1 == n /\ length l_2 = length l - n
    end)
    (decreases n)
=
  if n = 0 then ()
  else
    match l with
    | [] -> ()
    | _::xs -> splitAt_length (n-1) xs

let rec splitAt_assoc
  (#a:Type)
  (n1 n2:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l1, l2 = splitAt n1 l in
      let l2, l3 = splitAt n2 l2 in
      let l1', l2' = splitAt (n1+n2) l in
      l1' ==  l1 @ l2 /\ l2' == l3
    end)
    (decreases n1)
=
  if n1 = 0 then ()
  else
    match l with
    | [] -> ()
    | x :: xs -> splitAt_assoc (n1-1) n2 xs


let rec splitAt_length_total (#a:Type) (l:list a)
  : Lemma (requires True) (ensures (splitAt (length l) l == (l, []))) (decreases l)
=
  match l with
  | [] -> ()
  | x :: xs -> splitAt_length_total xs


(** If we [append] the two lists produced using a [splitAt], then we
    get back the original list *)
let rec lemma_splitAt_append (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires n <= length l)
    (ensures (let l1, l2 = splitAt n l in
              append l1 l2 == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> lemma_splitAt_append (n-1) xs


(** If we [splitAt] the point at which two lists have been [append]ed, then we
    get back the original lists. *)
let rec lemma_append_splitAt (#t:Type) (l1 l2:list t) :
  Lemma
    (ensures (splitAt (length l1) (append l1 l2) == (l1, l2))) =
  match l1 with
  | [] -> ()
  | _ -> lemma_append_splitAt (tl l1) l2


(** The [hd] of the second list returned via [splitAt] is the [n]th element of
    the original list *)
let rec lemma_splitAt_index_hd (#t:Type) (n:nat) (l:list t) :
  Lemma
    (requires (n < length l))
    (ensures (let l1, l2 = splitAt n l in
              splitAt_length n l;
              hd l2 == index l n)) =
  let x :: xs = l in
  match n with
  | 0 -> ()
  | _ -> lemma_splitAt_index_hd (n - 1) (tl l)


(** If two lists have the same left prefix, then shorter left prefixes are
    also the same. *)
let rec lemma_splitAt_shorten_left
    (#t:Type) (l1 l2:list t) (i:nat{i <= length l1 /\ i <= length l2}) (j:nat{j <= i}) :
  Lemma
    (requires (fst (splitAt i l1) == fst (splitAt i l2)))
    (ensures (fst (splitAt j l1) == fst (splitAt j l2))) =
  match j with
  | 0 -> ()
  | _ ->
    lemma_splitAt_shorten_left (tl l1) (tl l2) (i-1) (j-1)


(** Properties of split3 *)


(** The 3 pieces returned via [split3] can be joined together via an
    [append] and a [cons] *)
let rec lemma_split3_append (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        l == append a (b :: c))) =
  lemma_splitAt_append n l


(** The middle element returned via [split3] is the [n]th [index]ed element *)
let rec lemma_split3_index (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        b == index l n)) =
  lemma_splitAt_index_hd n l


(** The lengths of the left and right parts of a [split3] are as expected. *)
let rec lemma_split3_length (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires True)
    (ensures (
        let a, b, c = split3 l n in
        length a = n /\ length c = length l - n - 1)) =
  splitAt_length n l


(** If we [split3] on lists with the same left prefix, we get the same
    element and left prefix. *)
let lemma_split3_on_same_leftprefix
    (#t:Type) (l1 l2:list t) (n:nat{n < length l1 /\ n < length l2}) :
  Lemma
    (requires (fst (splitAt (n+1) l1) == fst (splitAt (n+1) l2)))
    (ensures (let a1, b1, c1 = split3 l1 n in
              let a2, b2, c2 = split3 l2 n in
              a1 == a2 /\ b1 == b2)) =
  let a1, b1, c1 = split3 l1 n in
  let a2, b2, c2 = split3 l2 n in
  lemma_split3_append l1 n;
  lemma_split3_append l2 n;
  lemma_split3_length l1 n;
  lemma_split3_length l2 n;
  append_l_cons b1 c1 a1;
  append_l_cons b2 c2 a2;
  // assert ((a1 @ [b1]) @ c1 == l1);
  // assert ((a2 @ [b2]) @ c2 == l2);
  let x1, y1 = splitAt (n+1) l1 in
  let x2, y2 = splitAt (n+1) l2 in
  lemma_splitAt_append (n+1) l1;
  lemma_splitAt_append (n+1) l2;
  splitAt_length (n+1) l1;
  splitAt_length (n+1) l2;
  // assert (x1 @ y1 == (a1 @ [b1]) @ c1);
  // assert (x2 @ y2 == (a2 @ [b2]) @ c2);
  append_length_inv_head x1 y1 (append a1 [b1]) c1;
  append_length_inv_head x2 y2 (append a2 [b2]) c2;
  // assert (a1 @ [b1] == a2 @ [b2]);
  append_length_inv_tail a1 [b1] a2 [b2];
  // assert (a1 == a2 /\ b1 == b2);
  ()


(** If we perform an [unsnoc] on a list, then the left part is the same
    as an [append]+[cons] on the list after [split3]. *)
let rec lemma_split3_unsnoc (#t:Type) (l:list t) (n:nat{n < length l}) :
  Lemma
    (requires (n <> length l - 1))
    (ensures (
        let a, b, c = split3 l n in
        lemma_split3_length l n;
        let xs, x = unsnoc l in
        let ys, y = unsnoc c in
        append a (b :: ys) == xs)) =
  match n with
  | 0 -> ()
  | _ -> lemma_split3_unsnoc (tl l) (n-1)


(** Doing [unsnoc] and [split3] in either order leads to the same left
    part, and element. *)
let rec lemma_unsnoc_split3 (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (requires (i <> length l - 1))
    (ensures (
        let xs, x = unsnoc l in
        lemma_unsnoc_snoc l;
        let a0, b0, c0 = split3 l i in
        let a1, b1, c1 = split3 xs i in
        a0 == a1 /\ b0 == b1)) =
  let xs, x = unsnoc l in
  lemma_unsnoc_snoc l;
  let a0, b0, c0 = split3 l i in
  let a1, b1, c1 = split3 xs i in
  splitAt_length_total xs;
  // assert (fst (splitAt (length xs) xs) == xs);
  // assert (fst (splitAt (length xs) xs) == fst (splitAt (length xs) l));
  // assert (i+1 <= length xs);
  lemma_splitAt_shorten_left xs l (length xs) (i+1);
  // assert (fst (splitAt (i+1) xs) == fst (splitAt (i+1) l));
  lemma_split3_on_same_leftprefix l xs i

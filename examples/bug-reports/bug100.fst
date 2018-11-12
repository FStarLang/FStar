module Bug100

(* run this with ../../bin/fstar.exe ../../lib/FStar.List.fst bug100.fst  *)

open List

(* this works *)
val append_length' :
  l1:list 'a -> l2:list 'a ->
  Lemma
    (requires True)
    (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_length' l1 l2 =
  match l1 with
  | []    -> ()
  | _::xs -> append_length' xs l2

(* but this doesn't *)
val append_length :
  l1:list 'a -> l2:list 'a ->
  Lemma
    (requires True)
    (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_length l1 l2 = by_induction_on l1 append_length

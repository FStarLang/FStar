module FStar.List.Pure.Properties

open FStar.List.Tot.Base
open FStar.List.Pure.Base
open FStar.List.Tot.Properties

(** Properties of splitAt *)

let rec splitAt_length (#a: Type) (n: nat) (l: list a)
  : Lemma (requires True)
    (ensures
      (let l_1, l_2 = splitAt n l in
        if length l < n
        then length l_1 == length l /\ length l_2 == 0
        else length l_1 == n /\ length l_2 = length l - n))
    (decreases n) =
  if n = 0
  then ()
  else
    match l with
    | [] -> ()
    | _ :: xs -> splitAt_length (n - 1) xs

let rec splitAt_assoc (#a: Type) (n1: nat) (n2: nat) (l: list a)
  : Lemma (requires True)
    (ensures
      (let l1, l2 = splitAt n1 l in
        let l2, l3 = splitAt n2 l2 in
        let l1', l2' = splitAt (n1 + n2) l in
        l1' == l1 @ l2 /\ l2' == l3))
    (decreases n1) =
  if n1 = 0
  then ()
  else
    match l with
    | [] -> ()
    | x :: xs -> splitAt_assoc (n1 - 1) n2 xs


let rec splitAt_length_total (#a: Type) (l: list a)
  : Lemma (requires True) (ensures (splitAt (length l) l == (l, []))) (decreases l) =
  match l with
  | [] -> ()
  | x :: xs -> splitAt_length_total xs


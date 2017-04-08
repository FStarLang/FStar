module FStar.List.Pure.Properties

open FStar.List.Tot.Base
open FStar.List.Pure.Base
open FStar.List.Tot.Properties

(** Properties of first_N *)

let rec first_N_length
  (#a:Type)
  (n:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l_1, l_2 = first_N n l in
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
    | _::xs -> first_N_length (n-1) xs

let rec first_N_assoc
  (#a:Type)
  (n1 n2:nat)
  (l:list a)
  : Lemma (requires True)
    (ensures begin
      let l1, l2 = first_N n1 l in
      let l2, l3 = first_N n2 l2 in
      let l1', l2' = first_N (n1+n2) l in
      l1' ==  l1 @ l2 /\ l2' == l3
    end)
    (decreases n1)
=
  if n1 = 0 then ()
  else
    match l with
    | [] -> ()
    | x :: xs -> first_N_assoc (n1-1) n2 xs


let rec first_N_length_total (#a:Type) (l:list a)
  : Lemma (requires True) (ensures (first_N (length l) l == (l, []))) (decreases l)
=
  match l with
  | [] -> ()
  | x :: xs -> first_N_length_total xs

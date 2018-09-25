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


let rec splitAt_append (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires n <= length l)
    (ensures (let l1, l2 = splitAt n l in
              append l1 l2 == l)) =
  match n with
  | 0 -> ()
  | _ ->
    match l with
    | [] -> ()
    | x :: xs -> splitAt_append (n-1) xs


let rec splitAt_index_hd (#t:Type) (n:nat) (l:list t) :
  Lemma
    (requires (n < length l))
    (ensures (let l1, l2 = splitAt n l in
              splitAt_length n l;
              hd l2 == index l n)) =
  let x :: xs = l in
  match n with
  | 0 -> ()
  | _ -> splitAt_index_hd (n - 1) (tl l)

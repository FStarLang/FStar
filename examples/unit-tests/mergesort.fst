module MergeSort

type mlist = list nat

(* borrowed from InsertionSort *)
val sorted: mlist -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> x <= y && sorted (y::xs)

val in_list: l:mlist -> n:nat -> Tot bool
let rec in_list l n = match l with
  | [] -> false
  | x::l' -> if x = n then true else in_list l' n

val length: l:mlist -> Tot nat
let rec length l = match l with
  | [] -> 0
  | x::l' -> 1 + length l'

(* val app: l1:mlist -> l2:mlist -> Pure mlist *)
(*                                  (requires True) *)
(*                                  (ensures (fun r -> *)
(* 				 (forall n. *)
(*                                   in_list r n <==> (in_list l1 n \/ in_list l2 n) *)
(*                                  ))) *)
(* let rec app l1 l2 = match l1 with *)
(*   | [] -> l2 *)
(*   | x::tl1 -> *)
(*     let r = app tl1 l2 in *)
(*     x::r *)


opaque type permutation (l1:mlist) (l2:mlist) = length l1 = length l2 /\
                                         (forall n. in_list l1 n == in_list l2 n)

opaque type permutation_2 (l:mlist) (l1:mlist) (l2:mlist) =
    (forall n. in_list l n == (in_list l1 n || in_list l2 n)) /\
    length l = length l1 + length l2

opaque type split_inv (l:mlist) (l1:mlist) (l2:mlist) =
    permutation_2 l l1 l2 /\ (* is_Cons l1 /\ is_Cons l2 *)
    (* needed for decreases clause in mergesort function *)
    length l > length l1 /\ length l > length l2

val split: l:mlist -> Pure (mlist * mlist)
                           (requires (is_Cons l /\ is_Cons (Cons.tl l)))
	                   (ensures (fun r -> split_inv l (fst r) (snd r)))
let rec split (x::y::l) =
  match l with
    | [] -> [x], [y]
    | [x'] -> x::[x'], [y]
    | _ ->
      let l1, l2 = split l in
      x::l1, y::l2

opaque type merge_inv (l1:mlist) (l2:mlist) (l:mlist) = (is_Cons l1 /\ is_Cons l /\ Cons.hd l1 = Cons.hd l) \/
                                                        (is_Cons l2 /\ is_Cons l /\ Cons.hd l2 = Cons.hd l) \/
                                                        (is_Nil l1 /\ is_Nil l2 /\ is_Nil l)

val merge: l1:mlist -> l2:mlist -> Pure mlist
                                   (requires (sorted l1 /\ sorted l2))
                                   (ensures (fun l -> sorted l 
                                                      /\ permutation_2 l l1 l2 
                                                      /\ merge_inv l1 l2 l))
let rec merge l1 l2 = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 ->
    if h1 <= h2 then
      let r = merge tl1 l2 in
      h1::r
    else
      let r = merge l1 tl2 in
      h2::r

val mergesort: l:mlist -> Pure mlist (requires True)
                                     (ensures (fun r -> sorted r /\ permutation l r))
                                     (decreases (length l))
let rec mergesort l = match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let (l1, l2) = split l in
    let sl1 = mergesort l1 in
    let sl2 = mergesort l2 in
    merge sl1 sl2


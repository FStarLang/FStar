module MergeSort
open FStar.List.Tot
open IntSort

type split_inv (l:list int) (l1:list int) (l2:list int) =
    permutation_2 l l1 l2 /\
    (* needed for decreases clause in mergesort function *)
    length l > length l1 /\ length l > length l2

val split: l:list int -> Pure (list int * list int)
             (requires (Cons? l /\ Cons? (Cons?.tl l)))
	     (ensures (fun r -> split_inv l (fst r) (snd r)))
let rec split (x::y::l) =
  match l with
    | [] -> [x], [y]
    | [x'] -> x::[x'], [y]
    | _ -> let l1, l2 = split l in
           x::l1, y::l2

(* Verification succeeds even without this invariant;
   it just takes a lot longer (22s vs 7s) *)
type merge_inv (l1:list int) (l2:list int) (l:list int) =
    (Cons? l1 /\ Cons? l /\ Cons?.hd l1 = Cons?.hd l) \/
    (Cons? l2 /\ Cons? l /\ Cons?.hd l2 = Cons?.hd l) \/
    (Nil? l1 /\ Nil? l2 /\ Nil? l)

val merge: l1:list int -> l2:list int -> Pure (list int)
             (requires (sorted l1 /\ sorted l2))
             (ensures (fun l -> sorted l /\ permutation_2 l l1 l2
                                         /\ merge_inv l1 l2 l))
#set-options "--z3rlimit 10"
let rec merge l1 l2 = match (l1, l2) with
  | [], _ -> l2
  | _, [] -> l1
  | h1::tl1, h2::tl2 -> if h1 <= h2
                        then h1::(merge tl1 l2)
                        else h2::(merge l1 tl2)

val mergesort: l:list int -> Pure (list int) (requires True)
      (ensures (fun r -> sorted r /\ permutation l r)) (decreases (length l))
let rec mergesort l = match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let (l1, l2) = split l in
    let sl1 = mergesort l1 in
    let sl2 = mergesort l2 in
    merge sl1 sl2

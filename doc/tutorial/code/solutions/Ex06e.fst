module Ex06e
//insertion-sort

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(* Definition of the [mem] function *)
val mem: int -> list int -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

(* A lemma to help Z3 *)
val sorted_smaller: x:int
                ->  y:int
                ->  l:list int
                ->  Lemma (requires (sorted (x::l) /\ mem y l))
                          (ensures (x <= y))
                          [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs

(* Insertion function *)
val insert : i:int -> l:list int{sorted l} -> Tot (m:list int{sorted m /\ (forall x. mem x m <==> x==i \/ mem x l)})
let rec insert i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then
       i::l
     else
       (* Solver implicitly uses the lemma: sorted_smaller hd (Cons.hd i_tl) tl *)
       hd::(insert i tl)

(* Insertion sort *)
val sort : l:list int -> Tot (m:list int{sorted m /\ (forall x. mem x l == mem x m)})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert x (sort xs)

module ListExercises

(* Definition of lists from prims.fst
type list 'a = 
  | Nil  : list 'a
  | Cons : hd:'a -> tl:list 'a -> list 'a
*)

// type nat = x:int{x>=0}

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val append_len: l1:list 'a -> l2:list 'a ->
      Tot (u:unit{length (append l1 l2) = length l1 + length l2})
(*    Lemma (requires True)
            (ensures (length (append l1 l2) = length l1 + length l2)) *)
let rec append_len l1 l2 = match l1 with
    | [] -> ()
    | hd::tl -> append_len tl l2

// ex 4a, 4b: types for append
// ex 4c: list membership
// ex 4d: reverse injective

let snoc l h = append l [h]

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
  | [] -> []
  | hd::tl -> snoc (reverse tl) hd

val snoc_cons: l:list 'a -> h:'a ->
      Lemma (reverse (snoc l h) = h::reverse l)
let rec snoc_cons l h = match l with
  | [] -> ()
  | hd::tl -> snoc_cons tl h 

val rev_involutive: l:list 'a ->
      Lemma (reverse (reverse l) = l)
let rec rev_involutive l = match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; snoc_cons (reverse tl) hd

(* l = hd::tl case
IH: reverse (reverse tl) = tl
TS: reverse (reverse (hd::tl)) = hd::tl
TS: reverse (snoc (reverse tl) hd) = hd::tl
By lemma
TS: hd::reverse (reverse tl) = hd::tl
By IH
TS: hd::tl = hd::tl
*)

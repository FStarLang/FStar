module Reverse

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

val snoc_cons: l:list 'a -> h:'a -> Lemma (reverse (snoc l h) = h::reverse l)
let rec snoc_cons l h = match l with
  | [] -> ()
  | hd::tl -> snoc_cons tl h 

val rev_involutive: l:list 'a -> Lemma (reverse (reverse l) = l)
let rec rev_involutive l = match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; snoc_cons (reverse tl) hd

(* Perhaps you did it like this: *)

val snoc_injective: l1:list 'a -> h1:'a -> l2:list 'a -> h2:'a 
                 -> Lemma (snoc l1 h1 = snoc l2 h2 ==> l1 = l2 && h1 = h2)
let rec snoc_injective l1 h1 l2 h2 = match l1, l2 with
  | _::tl1, _::tl2 -> snoc_injective tl1 h1 tl2 h2
  | _ -> ()

val rev_injective_1: l1:list 'a -> l2:list 'a 
                -> Lemma (reverse l1 = reverse l2 ==> l1 = l2)
let rec rev_injective_1 l1 l2 = match (l1, l2) with
  | hd1::tl1, hd2::tl2 ->
    rev_injective_1 tl1 tl2;
    snoc_injective (reverse tl1) hd1 (reverse tl2) hd2
  | _ -> ()

(* That's quite a tedious proof, isn't it. Here's a simpler proof. *)

val rev_injective_2: l1:list 'a -> l2:list 'a 
                 -> Lemma (reverse l1 = reverse l2 ==> l1 = l2)
let rev_injective_2 l1 l2 = rev_involutive l1; rev_involutive l2

(* The `rev_injective_2` proof is based on the idea that every involutive
function is injective. We've already proven that `reverse` is
involutive. So, we invoke our lemma, once for `l1` and once for `l2`.
This gives to the SMT solver the information that `reverse (reverse
l1) = l1` and `reverse (reverse l2) = l2`, which suffices to complete
the proof. As usual, when structuring proofs, lemmas are your friends! *)

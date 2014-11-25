module Reverse

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function 
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

val rev_injective_1: l1:list 'a -> l2:list 'a 
                -> Lemma (reverse l1 = reverse l2 ==> l1 = l2)

module Mem

val mem: 'a -> list 'a -> Tot bool

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val append_mem:  l1:list 'a -> l2:list 'a -> a:'a
        -> Lemma (ensures (mem a (append l1 l2) <==>  mem a l1 || mem a l2))
let append_mem l1 l2 a = ()

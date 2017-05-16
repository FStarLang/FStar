module Ex04c
//mem

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x xs =
  match xs with
  | [] -> false
  | hd::tl -> hd=x || mem x tl

val append_mem:  #a:eqtype -> l1:list a -> l2:list a -> x:a
        -> Lemma (ensures (mem x (append l1 l2) <==>  mem x l1 || mem x l2))
// BEGIN: AppendMemProof
let rec append_mem #a l1 l2 x =
  match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 x
// END: AppendMemProof

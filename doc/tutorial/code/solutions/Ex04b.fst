module Ex04b
//append-extrinsic-lemma

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val append_len: l1:list 'a -> l2:list 'a 
         -> Lemma (requires True)
                  (ensures (length (append l1 l2) = length l1 + length l2))
let rec append_len l1 l2 =
  match l1 with 
   | [] -> ()
   | hd::tl -> append_len tl l2

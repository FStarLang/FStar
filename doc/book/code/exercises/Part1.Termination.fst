module Part1.Termination

//Remove the admits and add the right decreases annotations

let rec fib (a b n:nat)
  : Tot nat
  = admit();
    match n with
    | 0 -> a
    | _ -> fib b (a+b) (n-1)

let fibonacci (n:nat) : nat = fib 1 1 n

let rec rev_aux #a (l1 l2:list a)
  : Tot (list a)
  = admit();
    match l2 with
    | []     -> l1
    | hd :: tl -> rev_aux (hd :: l1) tl

let rev #a (l:list a) : list a = rev_aux [] l

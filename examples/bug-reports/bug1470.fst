module Bug1470

val length : list 'a -> Dv nat
let rec length l =
  match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

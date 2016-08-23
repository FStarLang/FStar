module Ex04h
//nth

val length : list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl

val nth : l:list 'a -> n:nat{op_LessThan n (length l)} -> Tot 'a
let rec nth l n =
  match l with
  | h :: t -> if n = 0 then h else nth t (n-1)

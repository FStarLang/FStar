module Part1.Inductives

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

val append (#a:Type) (l1 l2:list a)
  : l:list a { length l = length l1 + length l2 }
let append = admit()

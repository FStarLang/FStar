module Part1.Inductives

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl


let rec append #a (l1 l2: list a)
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

module Bug1360

let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

module Bug818

val find : ('a -> Tot bool) -> Tot ((list 'a) -> Tot (option 'a))
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl


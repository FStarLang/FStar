module Bug1360

#set-options "--use_two_phase_tc true"

let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

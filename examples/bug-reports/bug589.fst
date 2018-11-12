module Bug589

assume val g: list 'a -> Tot unit
let f l =
  let _ = g l in
  let rec aux l = l in
  aux l

let h l =
  let rec aux l =
    match l with
    | [] -> ()
    | hd::tl -> aux tl
  in
  aux l

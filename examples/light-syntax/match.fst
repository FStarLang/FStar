#light "on"
module Match

let f l1 l2 =
  match l1 with
  | [] ->
    match l2 with
    | [] -> 0
    | hd::tl -> 1
  | _ -> 2

let rec fib = function
  | 0 | 1 -> 1
  | n -> fib (n - 1) + fib (n - 2)

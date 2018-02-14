module A

let rec foo :list int -> Tot int = fun l -> match l with
  | [] -> 0
  | _  -> 1


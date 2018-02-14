module B

val foo: list int -> Tot int
let rec foo l = match l with
  | [] -> 0
  | _  -> 1

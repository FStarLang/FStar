module Bug466

val move_refinement : l:list int -> Tot (r:(list (x:int{True})){r == l})
let rec move_refinement l =
  match l with
  | [] -> []
  | _  -> magic()

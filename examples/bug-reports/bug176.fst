module Bug176

let foo xs =
  match xs with
  | []
  | x::xs' -> x

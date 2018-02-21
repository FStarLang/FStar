module Bug028

val typing : int
let typing =
  match 41, 42, Some 43 with
  | 41, 42, Some 43 -> 0
  | _, _, _         -> 0

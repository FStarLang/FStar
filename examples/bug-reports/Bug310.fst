module Bug310
val r: unit -> a:Type -> f:(a -> a) -> int
let r _ _ _ = 0

val g: int -> int -> int
let g _ _ = 0

val ko: int -> Tot int
let ko a =
  let a21 = a in
  r () int (g a21)


let test =
  let x = 0 in
  [@inline_let] let y = x in
  let x = 2 in
  (y, x)

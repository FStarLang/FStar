module SizeT

open FStar.SizeT

let f () =
  let x = mk 0us in
  let y = mk 1us in
  let z = x +^ y in
  let z = z -^ x in
  let z = z *^ y in
  if z <=^ x then
    zero
  else
    one

let g () =
  let x = mk_checked 500000uL in
  x

let main () : Int32.t =
  let x = f () in
  let y = g () in
  if x = y then 1l
  else 0l

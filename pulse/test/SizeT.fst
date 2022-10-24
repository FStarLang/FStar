module SizeT

open FStar.SizeT

let f () =
  let x = mk 0us in
  let y = mk 1us in
  let z = x `add` y in
  let z = z `sub` x in
  let z = z `mul` y in
  if z `le` x then
    zero
  else
    one

let g () =
  let x = mk_checked 500000uL in
  x

let main () : t * t =
  let x = f () in
  let y = g () in
  x, y

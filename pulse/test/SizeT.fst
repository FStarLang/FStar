module SizeT

open FStar.SizeT

let f () =
  let x = 0sz in
  let y = 1sz in
  assert (fits (v y));
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

open FStar.PtrdiffT

let ft () =
  let x = mk 0s in
  let y = mk 1s in
  let z = x +^ y in
  if z <=^ x then zero else zero

let main () : Int32.t =
  let x = f () in
  let y = g () in
  let z = ft () in
  if x = y then 1l
  else
    if z >^ zero then 1l
    else 0l

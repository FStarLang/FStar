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
    0sz
  else
    1sz

open FStar.PtrdiffT

let ft () =
  let x = mk 0s in
  let y = mk 1s in
  let z = x +^ y in
  if z <=^ x then zero else zero

open Steel.Effect
open Steel.Array

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let x = f () in
  intro_fits_u32 ();
  let y = of_u32 500000ul in
  let z = ft () in
  if x = y then 1l
  else
    if z >^ zero then 1l
    else 0l

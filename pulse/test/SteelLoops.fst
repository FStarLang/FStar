module SteelLoops

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
open Steel.Loops

let sum_to_n_for (r:ref UInt32.t) : SteelT unit (vptr r) (fun _ -> vptr r) =
  for_loop
    0ul
    10ul
    (fun _ -> vptr r)
    (fun _ -> let x = read r in write r (x `FStar.UInt32.add_mod` 1ul))

let sum_to_n_while (r:ref UInt32.t) : SteelT unit (vptr r) (fun _ -> vptr r) =
  intro_exists (Ghost.hide true) (fun _ -> vptr r);
  while_loop
    (fun _ -> vptr r)
    (fun _ ->
      let _ = witness_exists () in
      let n = read r in
      FStar.UInt32.lt n 10ul
    )
    (fun _ ->
      let n = read r in
      write r (n `FStar.UInt32.add_mod` 1ul);
      intro_exists (Ghost.hide true) (fun _ -> vptr r)
    )

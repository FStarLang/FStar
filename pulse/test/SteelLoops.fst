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

let sum_to_n_for_2 (r:ref UInt32.t) : Steel unit (vptr r) (fun _ -> vptr r)
  (requires fun h -> sel r h == 0ul)
  (ensures fun h0 _ h1 -> sel r h1 == 10ul)
=
  for_loop_full
    0ul
    10ul
    (fun _ -> vptr r)
    (fun i v -> v == UInt32.uint_to_t i)
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

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let r = malloc 0ul in
  sum_to_n_for r;
  sum_to_n_while r;
  free r;
  return 0l

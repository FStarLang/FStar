module Selectors.Examples

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

/// A few small tests for the selector effect.

#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"

let swap (#a:Type0) (r1 r2:ref a) : Steel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h0 == sel r2 h1 /\
    sel r2 h1 == sel r1 h1)
  = let x1 = read r1 in
    let x2 = read r2 in
    write r2 x1;
    write r1 x2

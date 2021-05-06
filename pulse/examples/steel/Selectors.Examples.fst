module Selectors.Examples

open Steel.SelEffect.Atomic
open Steel.SelEffect
open Steel.SelReference

(* Some tests *)

#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"

let swap (#a:Type0) (r1 r2:ref a) : SteelSel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h0 == sel r2 h1 /\
    sel r2 h0 == sel r1 h1)
  = let x1 = read r1 in
    let x2 = read r2 in
    write r2 x1;
    write r1 x2

let test0 (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun h -> sel r h == 0)
  (ensures fun _ _ h1 -> sel r h1 == 1)
  = let h = get () in
    assert (sel r h == 0);
    write r 1;
    let h1 = get() in
    assert (sel r h1 == 1);
    write r 1

let test1 (r:ref int) : SteelSel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel r h1 == 0)
  = write r 1;
    write r 0;
    ()

let test2 (r1 r2:ref int) : SteelSel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun h -> sel r1 h == 1)
  (ensures fun h0 _ h1 -> sel r1 h1 == 0 /\ sel r2 h0 == sel r2 h1)
  = write r1 0;
    write r1 0

let test3 (r1 r2 r3:ref int) : SteelSel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h1 == 0 /\
    sel r2 h0 == sel r2 h1 /\
    sel r3 h0 == sel r3 h1
  )
  = let h0 = get () in
    write r1 1;
    let h1 = get() in
    assert (sel r1 h1 == 1);
    assert (sel r2 h0 == sel r2 h1);
    write r1 0

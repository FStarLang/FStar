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
    sel r2 h0 == sel r1 h1)
  = let x1 = read r1 in
    let x2 = read r2 in
    write r2 x1;
    write r1 x2

let test0 (r:ref int) : Steel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun h -> sel r h == 0)
  (ensures fun _ _ h1 -> sel r h1 == 1)
  = let x = gget (vptr r) in
    assert (x == Ghost.hide 0);
    write r 1;
    let x = gget (vptr r) in
    assert (x == Ghost.hide 1);
    write r 1

let test1 (r:ref int) : Steel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel r h1 == 0)
  = write r 1;
    write r 0

let test2 (r1 r2:ref int) : Steel unit
  (vptr r1 `star` vptr r2) (fun _ -> vptr r1 `star` vptr r2)
  (requires fun h -> sel r1 h == 1)
  (ensures fun h0 _ h1 -> sel r1 h1 == 0 /\ sel r2 h0 == sel r2 h1)
  = write r1 0;
    write r1 0

let test3 (r1 r2 r3:ref int) : Steel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h1 == 0 /\
    sel r2 h0 == sel r2 h1 /\
    sel r3 h0 == sel r3 h1
  )
  = let x2_0 = gget (vptr r2) in
    write r1 1;
    let x1_1 = gget (vptr r1) in
    let x2_1 = gget (vptr r2) in
    assert (x1_1 == Ghost.hide 1);
    assert (x2_0 == x2_1);
    write r1 0

let test4 (r: ref nat) : SteelT unit (vptr r) (fun _ -> vptr r) =
  share r;
  gather r

let rec test5 (#p: Steel.FractionalPermission.perm) (r: ref nat) (n: nat) () : SteelT unit (vptrp r p) (fun _ -> vptrp r p) =
  if n = 0
  then return ()
  else begin
    let j = n - 1 in
    share r;
    let _ = par
      (test5 r j) // FIXME: does not work with (fun _ -> test5 r j ()): computed SteelBase, expected SteelT
      (test5 r j)
    in
    gather r
  end

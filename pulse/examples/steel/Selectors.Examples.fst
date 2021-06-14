module Selectors.Examples

// open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

/// A few small tests for the selector effect.

#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"

module T = FStar.Tactics

#set-options "--print_full_names --log_queries"

let debug(r r':ref int) : Steel unit
  (vptr r `star` vptr r') (fun _ -> vptr r `star` vptr r')
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> sel r h1 == 0)
  by (T.norm normal_steps; T.dump "here")
  = write r 1;
    write r 0

(*
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
  = let h = get () in
    assert (sel r h == 0);
    write r 1;
    let h1 = get() in
    assert (sel r h1 == 1);
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

module T = FStar.Tactics

let test3 (r1 r2 r3:ref int) : Steel unit
  (vptr r1 `star` (vptr r2 `star` vptr r3)) (fun _ -> vptr r1 `star` (vptr r2 `star` vptr r3))
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h1 == 0 /\
    sel r2 h0 == sel r2 h1 /\
    sel r3 h0 == sel r3 h1
  )
  by (T.norm normal_steps)
  = let h0 = get () in
    write r1 1;
    let h1 = get() in
    assert (sel r1 h1 == 1);
    assert (sel r2 h0 == sel r2 h1);
    write r1 0
*)

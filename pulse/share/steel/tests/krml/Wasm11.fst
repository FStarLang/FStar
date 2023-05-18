module Wasm11

open FStar.SizeT
open FStar.PtrdiffT
open FStar.UInt64
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array

(* WASM tests for pointer subtraction *)

let test1 () : SteelT bool emp (fun _ -> emp) =
  let r = malloc 0uL 8sz in
  ghost_split r 4sz;
  let r1 = split_l r 4sz in
  let r2 = split_r r 4sz in
  change_equal_slprop (varray (split_l r 4sz)) (varray r1);
  change_equal_slprop (varray (split_r r 4sz)) (varray r2);
  let _ = mk 4s in
  let b = ptrdiff r2 r1 in
  ghost_join r1 r2 ();
  change_equal_slprop
    (varray (merge r1 r2))
    (varray r);
  // Free not supported in Wasm
  drop (varray r);
  return (b = mk 4s)

type t = { foo: UInt32.t; bar: UInt16.t }

inline_for_extraction noextract
let def_t : t = { foo = 0ul; bar = 0us }

let test2 () : SteelT bool emp (fun _ -> emp) =
  let r = malloc def_t 8sz in
  ghost_split r 4sz;
  let r1 = split_l r 4sz in
  let r2 = split_r r 4sz in
  change_equal_slprop (varray (split_l r 4sz)) (varray r1);
  change_equal_slprop (varray (split_r r 4sz)) (varray r2);
  let _ = mk 4s in
  let b = ptrdiff r2 r1 in
  ghost_join r1 r2 ();
  change_equal_slprop
    (varray (merge r1 r2))
    (varray r);
  // Free not supported in wasm
  drop (varray r);
  return (b = mk 4s)

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let res1 = test1 () in
  let res2 = test2 () in
  if res1 && res2 then 0l else 1l

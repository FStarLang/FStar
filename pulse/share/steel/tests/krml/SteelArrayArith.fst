module SteelArrayArith

open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
open Steel.ArrayArith

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let r = malloc 0ul 3sz in
  ghost_split r 1sz;
  let r1 = split_r r 1sz in
  change_equal_slprop (varray (split_r r 1sz)) (varray r1);
  ghost_split r1 1sz;
  let r2 = split_r r1 1sz in
  change_equal_slprop (varray (split_r r1 1sz)) (varray r2);
  let b = within_bounds_intro (split_l r 1sz) (split_l r1 1sz) r2 in
  ghost_join (split_l r1 1sz) r2 ();
  change_equal_slprop
    (varray (merge (split_l r1 1sz) r2))
    (varray r1);
  ghost_join (split_l r 1sz) r1 ();
  change_equal_slprop
    (varray (merge (split_l r 1sz) r1))
    (varray r);
  free r;
  if b then 0l else 1l

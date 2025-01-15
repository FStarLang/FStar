module FStarC.GenSym

module Util = FStarC.Util

(* private *)
let gensym_st = Util.mk_ref 0

let next_id () =
  let r = !gensym_st in
  gensym_st := r + 1;
  r

let reset_gensym () = gensym_st := 0

let with_frozen_gensym f =
  let v = !gensym_st in
  let r =
    try f () with
    | e -> (gensym_st := v; raise e)
  in
  gensym_st := v;
  r

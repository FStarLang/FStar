module BangBang
open Pulse
#lang-pulse

fn modify_nested_ptr (x: ref (ref Int32.t)) (#y: erased (ref Int32.t)) (#z: erased Int32.t { Int32.v z < Int.max_int Int32.n - 3 })
  preserves x |-> y
  requires reveal y |-> z
  returns z': Int32.t
  ensures reveal y |-> Int32.add z 2l
  ensures rewrites_to z' (Int32.add z 3l)
{
  (!x) := (!(!x)) `Int32.add` 2l;
  ((!(!x)) `Int32.add` 1l)
}

fn decr_uint () {
  let mut x: UInt32.t = 1ul;
  x := !x `UInt32.sub` 1ul;
}

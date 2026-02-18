module Defer
#lang-pulse
open Pulse
module V = Pulse.Lib.Vec

fn without_defer (x: bool) {
  let v = V.alloc 1uy 10sz;
  if (x) {
    V.free v;
    return;
  };
  V.free v;
}

fn with_defer (x: bool) {
  let v = V.alloc 1uy 10sz;
  defer live v { V.free v };
  if (x) {
    return;
  };
}
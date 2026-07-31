module Bug583
open Pulse
#lang-pulse

divergent fn problem () {
  let mut i = 0sz;
  let mut j = 1sz;
  while ((!j `SizeT.sub` !i) <> 0sz)
    invariant live i
    invariant live j
    invariant pure (!i `SizeT.lte` !j)
  {}
}
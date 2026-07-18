module Bug4280

#lang-pulse
open Pulse

let predicate foo ([@@@mkey] r : ref int) (x : int) =
  r |-> x

#check foo

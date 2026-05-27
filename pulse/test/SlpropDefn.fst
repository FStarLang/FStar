module SlpropDefn
open Pulse
#lang-pulse

let predicate foo (x: ref int) = live x ** pure (!x > 10)

let foo_spec (x: ref int) = assert_norm (foo x == exists* (y: int). x |-> y ** pure (y > 10))
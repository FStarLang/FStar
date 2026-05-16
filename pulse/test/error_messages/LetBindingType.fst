module LetBindingType
#lang-pulse
open Pulse.Lib.Pervasives

// Let binding with wrong type annotation
[@@expect_failure [189]]
fn let_binding_type ()
  requires emp
  ensures emp
{
  let x : bool = 42;
  ()
}

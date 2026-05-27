module BindTypeMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Binding with wrong type annotation
fn helper ()
  requires emp
  returns r: int
  ensures emp
{
  42
}

[@@expect_failure [228]]
fn bind_type_err ()
  requires emp
  ensures emp
{
  let x : bool = helper ();  // ERROR: helper returns int, binding expects bool
  ()
}

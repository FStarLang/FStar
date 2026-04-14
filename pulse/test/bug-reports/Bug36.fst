module Bug36

#lang-pulse
open Pulse

[@@expect_failure [189]]
fn foo
  (n : nat) // error shown here: Expected expression of type Type got expression n of type nat
  returns m:nat
  ensures pure (m == n)
{
  id #n // <- but the issue is here
}

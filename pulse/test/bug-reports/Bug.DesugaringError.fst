module Bug.DesugaringError

#lang-pulse
open Pulse.Lib.Pervasives

[@@expect_failure]
fn test (x:nat) (y:nat) 
{
    a ; an ()
}

[@@expect_failure]
ghost
fn test2 (x:something)
{
    ()
}

let id (#a:Type) (x y:a) = x

[@@expect_failure]
fn test3 (x:nat) (y:bool)
returns z:nat
{
    id x y
}

fn f (x: nat)
{
  ()
}

[@@expect_failure]
fn test4 ()
{
  f true
}

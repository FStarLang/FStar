module Bug.DesugaringError

#lang-pulse
open Pulse.Lib.Pervasives

[@@expect_failure]
fn test (x:nat) (y:nat) 
requires emp
ensures emp
{
    a ; an ()
}

[@@expect_failure]
ghost
fn test2 (x:something)
requires emp
ensures emp
{
    ()
}

let id (#a:Type) (x y:a) = x

[@@expect_failure]
fn test3 (x:nat) (y:bool)
requires emp
returns z:nat
ensures emp
{
    id x y
}

fn f (x: nat)
requires emp
ensures emp
{
  ()
}

[@@expect_failure]
fn test4 ()
requires emp
ensures emp
{
  f true
}

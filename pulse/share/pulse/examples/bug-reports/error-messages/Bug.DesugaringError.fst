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
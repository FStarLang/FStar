module Test.GenOrder2.B

#lang-pulse
open Pulse
open Test.GenOrder2.A

fn test ()
  requires foo 1 2
  ensures  foo 2 1
{
  flip () #1 #2;
}

module NormCtx

#lang-pulse
open Pulse.Nolib

assume val foo : slprop
let bar : slprop = foo

let norm_bar = norm [delta] #slprop bar

fn test ()
  requires norm_bar
  ensures  foo
{
  unfold norm_bar;
  ();
}

fn test2 ()
  requires norm [delta] #slprop bar
  ensures  foo
{
  ();
}

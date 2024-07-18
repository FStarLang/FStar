module PulseTest.UseLang
#lang-pulse
open FStar.Mul
open Pulse.Lib.Pervasives
let x = 0
let y = 1
let z = x + y 
let w = z
let t = 0

fn return_z ()
requires emp
returns r:int
ensures pure (r == z)
{
    z
}

let some = 1
let foobar = 17 

fn return_2z ()
requires emp
returns r:int
 
ensures pure (r == 2 * z)
{
  let v = return_z ();
  (v + x + y)
}
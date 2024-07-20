module PulseTest.UseLang
#lang-pulse
open Pulse.Lib.Pervasives

fn double (x:ref int)
requires pts_to x 'v
ensures pts_to x ('v + 'v)
{
  open FStar.Mul; //dependence scanning works inside Pulse
  let v = !x;
  x := 2 * v;
}

let x = 0

let y = 1

let z = x + y
#lang-pulse
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
ensures pure (FStar.Mul.(r == 2 * z)) //dep scanning inside Pulse
{
  let v = return_z ();
  (v + x + y)
}

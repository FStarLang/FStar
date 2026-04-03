module ANF

#lang-pulse
open Pulse

fn test ()
{
  let mut r = 0;
  r := !r + 1;
  r := !r + 1;
  r := !r + 1;
  r := !r + 1;
}

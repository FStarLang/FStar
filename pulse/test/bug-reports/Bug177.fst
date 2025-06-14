module Bug177

#lang-pulse
open Pulse

fn kswap_int
  (r : ref int)
  requires pts_to r 'v
  ensures  pts_to r 'v
{
  r := !r;
}

fn kswap_t
  (#t : Type0)
  (r : ref t)
  requires pts_to r 'v
  ensures  pts_to r 'v
{
  r := !r;
}
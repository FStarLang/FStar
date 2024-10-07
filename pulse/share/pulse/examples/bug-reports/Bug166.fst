module Bug166
open Pulse
#lang-pulse

inline_for_extraction noextract
fn h ()
  requires emp
  returns  x : int
  ensures  emp
{
  42
}
let h2 = h
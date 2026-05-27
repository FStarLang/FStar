module Bug166
open Pulse
#lang-pulse

inline_for_extraction noextract
fn h ()
  returns  x : int
{
  42
}
let h2 = h
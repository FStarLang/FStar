module AtomicMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Using non-atomic operation in atomic context
[@@expect_failure [228]]
atomic
fn atomic_fn (r: ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  r := 1;  // Might error if := is not atomic-compatible
  ()
}

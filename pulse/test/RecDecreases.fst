module RecDecreases
open Pulse
#lang-pulse

fn rec count_down (x:nat)
returns i:nat
ensures pure (i == 0)
decreases x
{
  if (x = 0) { x }
  else { count_down (x - 1) }
}

[@@expect_failure]
ghost fn rec ghost_rec_decreases_checked_ok (x:nat)
returns i:nat
ensures pure (i == 0)
decreases x
{
  if (x = 0) { x }
  else { ghost_rec_decreases_checked_ok (x + 1) }
}

[@@expect_failure]
fn rec bug_concrete_rec_decreases_unchecked (x:nat)
returns i:nat
ensures pure (i == 0)
decreases x
{
  if (x = 0) { x }
  else { bug_concrete_rec_decreases_unchecked (x + 1) }
}

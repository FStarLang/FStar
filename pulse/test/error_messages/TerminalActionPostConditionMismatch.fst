module TerminalActionPostConditionMismatch
#lang-pulse
open Pulse.Lib.Pervasives

// Terminal action with postcondition that doesn't match the actual state
[@@expect_failure [19]]
fn terminal_action_mismatch (r: ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  r := 0;
  r := 2;
}

// Same error, with explicit () at end — both should localize to r := 2
[@@expect_failure [19]]
fn terminal_action_mismatch_localized (r: ref int)
  requires pts_to r 0
  ensures pts_to r 1
{
  r := 0;
  r := 2;
  ()
}
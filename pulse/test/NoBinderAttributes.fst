module NoBinderAttributes

#lang-pulse
open Pulse

// Binder attributes are meaningful on a named binder (see RenameLet.fst), but
// there is no binder to attach them to on a wildcard.
[@@expect_failure]
fn test ()
{
  let [@@@123] _ = 1;
  ();
}

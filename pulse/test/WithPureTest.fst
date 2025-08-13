module WithPureTest
open Pulse
open Pulse.Lib.WithPure
#lang-pulse

ghost fn intro_test (p: slprop) (q: prop)
  requires p
  requires pure q
  ensures with_pure q (fun _ -> with_pure (~ (~q)) fun _ -> p)
{ () }

ghost fn elim_test (p: slprop) (q: prop)
  requires no_extrude (with_pure q (fun _ -> p))
  ensures p
  ensures pure q
{ () }

[@@expect_failure [19]]
ghost fn cant_intro_false ()
  ensures with_pure False (fun _ -> emp)
{ () }

[@@expect_failure [228]]
ghost fn cant_intro_missing_resource (p: slprop)
  ensures with_pure True (fun _ -> p)
{ () }

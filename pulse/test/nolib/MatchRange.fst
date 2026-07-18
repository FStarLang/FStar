module MatchRange

#lang-pulse
open Pulse.Nolib

[@@expect_failure [19]]
fn completeness_err2 (x : list int)
{
  ();
  ();
  ();
  ();
  let hd::tl = x;
  ();
  ();
  ();
  ();
  ();
}

[@@expect_failure [19]]
fn completeness_err1 (x : list int)
{
  ();
  ();
  ();
  ();
  match x {
    hd :: tl -> {
      ();
    }
  };
}

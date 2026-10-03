module CommentTest
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Comment

fn test (x: UInt32.t)
  returns y : UInt32.t
{
  comment "this is a standalone comment";
  let mut r = comment_gen "before the initial value" x "after the initial value";
  let v = !r;
  r := v;
  comment "this is another standalone comment";
  comment_gen "before the result" 42ul "after the result"
}

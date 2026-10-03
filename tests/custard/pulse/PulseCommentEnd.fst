(* Section 120.  A comment whose text contains the end-of-comment marker
   would close early and leave its tail to be compiled as code.  Refused at
   the rule, which is the last place the string is still known to be the
   literal the author wrote. *)
module PulseCommentEnd
#lang-pulse
open Pulse
open Pulse.Lib.Comment
module I32 = FStar.Int32

fn main () requires emp returns c: I32.t ensures emp
{
  comment "this ends it */ and this is code";
  0l
}

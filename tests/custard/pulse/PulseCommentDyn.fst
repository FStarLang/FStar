(* Section 120.  The text becomes a comment in the generated code, so there
   is nowhere to evaluate it: it has to be a literal.  [dyn] is a definition
   rather than a literal, and it is not [inline_for_extraction], so nothing
   reduces it away. *)
module PulseCommentDyn
#lang-pulse
open Pulse
open Pulse.Lib.Comment
module I32 = FStar.Int32

let dyn : string = FStar.String.concat "" ["computed"; " text"]

fn main () requires emp returns c: I32.t ensures emp
{
  comment dyn;
  0l
}

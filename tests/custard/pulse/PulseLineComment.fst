(* --custard_line_comments on the comment texts PulseComment does not have:
   one spanning two lines, an empty one, and one whose line ends in a
   backslash, which must stay a block comment -- a line comment would splice
   the next source line into itself. *)
module PulseLineComment
#lang-pulse
open Pulse
open Pulse.Lib.Comment
module U32 = FStar.UInt32
module I32 = FStar.Int32

fn step (x: U32.t)
  returns y: U32.t
{
  comment "first line\n   second line, indented";
  comment "";
  comment "ends in a backslash \\";
  let y = U32.add_mod x 1ul;
  comment "after the addition";
  y
}

fn main () returns c: I32.t
{
  let y = step 1ul;
  if (U32.eq y 2ul) { 0l } else { 1l }
}

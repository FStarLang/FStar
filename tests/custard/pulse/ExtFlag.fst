module ExtFlag
#lang-pulse
open Pulse
open FStar.Attributes
module I32 = FStar.Int32

(* Section 61.2.  An extern's name is one *preprocessing* token, not one.

   Section 59.4 let [group] leave "an identifier or an integer literal"
   unparenthesized, on the ground that one token cannot be bound into.  A
   name is one token only until it is expanded, and the names Custard does
   not write are exactly the extern ones -- their declarations are in a
   header this backend never sees.  Section 59.5 had already drawn this
   conclusion for the sibling question, keeping casts on extern arguments
   because such a name may be a macro; the parenthesis is the same question
   and did not get the same answer.

   The stub defines [EXT_FLAG] as [0 || 1], which is what a macro looks
   like when it is an expression rather than a value.  Unparenthesized,
   [!EXT_FLAG] is [!0 || 1] -- true regardless -- and silent under
   [-Wall -Wextra].

   **Both negation sites are here on purpose**, because they were broken
   for two different reasons and a test hitting one would have missed the
   other.  [cond_site] reaches [negate], which does call [group] and so was
   fixed by [is_atom]; [expr_site] reaches the [!] of an ordinary
   expression, which printed its operand bare and never called [group] at
   all -- that half is older than section 59.  The [if ... then () else]
   with an empty then-branch is what forces the first, and it is the same
   lesson as ExtBuf: the obvious spelling tests the wrong site. *)

[@@custard_extern "EXT_FLAG"; custard_c_header "ExtFlag_stubs.h"]
assume val ext_flag : bool

let expr_site () : I32.t = if not ext_flag then 0l else 1l

fn cond_site ()
  returns res : I32.t
{
  let mut r = 1l;
  if ext_flag { () } else { r := 0l };
  !r
}

fn main ()
  returns res : I32.t
{
  let a = expr_site ();
  let b = cond_site ();
  if (I32.eq a 1l && I32.eq b 1l) { 0l } else { 1l }
}

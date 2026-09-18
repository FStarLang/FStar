module CompileTimeBad

(* Section 30.10.  The other half of CompileTime: [@@custard_compile_time] is a
   promise, and a promise that is not kept is an error rather than a quiet
   fall-back to compiling the definition.

   Falling back would be the worse behaviour precisely where the attribute is
   useful: without it, [string_length] compiles, and drags a [list char] into a
   C program that has no representation for one.  The reader would then be told
   about a list they never wrote, in a definition they did not know was
   involved, instead of about the one call whose argument was not a constant.

   The check is on the application as written, not on the reduct.  Unfolding
   removes the head whether or not anything was computed -- [string_length s]
   for an unknown [s] reduces to the [match] in its body, headed by nothing --
   so a test on the reduct's head would pass exactly this case. *)

open FStar.Attributes

module U32 = FStar.UInt32

[@@custard_compile_time]
let string_length (x: string) : nat =
  FStar.List.Tot.length (FStar.String.list_of_string x)

let use (s: string) : U32.t =
  if string_length s = 5 then 0ul else 1ul

module DevGuardBad
module I32 = FStar.Int32
open FStar.Attributes

/// Section 51.6.  A [custard_c_ifdef] flag is a preprocessor condition, and
/// C has those only in [#if]; any use but the whole condition of an [if] is
/// refused.

[@@custard_c_ifdef "defined(__x86_64__)"]
assume val x86 : bool

let main () : I32.t = if not x86 then 0l else 1l

module ExtractAs
open FStar.ExtractAs
let fail_unless (b: bool) = if b then "ok" else magic ()

// Test that extract_as works when extracting the definition itself.

[@@extract_as (`(fun (x: nat) -> x + 10))]
let frob y = 2 + y

#push-options "--warn_error -272" //Warning_TopLevelEffect
let _ = fail_unless (frob 1 = 11)
#pop-options

// Test that extract_as works when inlining the definition.

inline_for_extraction noextract [@@extract_as (`(fun (x: nat) -> x + 10))]
let bar_2 y = 2 + y
let bar z = bar_2 z

#push-options "--warn_error -272" //Warning_TopLevelEffect
let _ = fail_unless (bar 1 = 11)
#pop-options


// It also works if the definition is recursive

[@@extract_as (`(fun (x: nat) -> x))]
let rec loopid (x:nat) : Dv nat = loopid x

// Recursion in the source must not block a nonrecursive replacement.
inline_for_extraction noextract [@@extract_as (`(fun (x: nat) -> x))]
let rec inline_loopid (x:nat) : Dv nat = inline_loopid x

#push-options "--warn_error -272" //Warning_TopLevelEffect
(* Masking the effect of a top-level definition requires proving its
   type inhabited; see issue #4401. *)
let _ : nonempty nat = nonempty_intro 0
let two = loopid 2
let two_inline = inline_loopid 2
let _ = fail_unless (two_inline = 2)
#pop-options
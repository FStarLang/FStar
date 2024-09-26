module ExtractAs
open FStar.ExtractAs
let fail_unless (b: bool) = if b then "ok" else magic ()

// Test that extract_as works when extracting the definition itself.

[@@extract_as (`(fun (x: nat) -> x + 10))]
let frob y = 2 + y

let _ = fail_unless (frob 1 = 11)

// Test that extract_as works when inlining the definition.

inline_for_extraction noextract [@@extract_as (`(fun (x: nat) -> x + 10))]
let bar_2 y = 2 + y
let bar z = bar_2 z

let _ = fail_unless (bar 1 = 11)

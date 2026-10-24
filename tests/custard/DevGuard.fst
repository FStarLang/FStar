module DevGuard
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

/// Section 51.6.  Code for one architecture, behind the preprocessor.
///
/// A [target("avx2")] function does not compile for ARM, so [fancy] and the
/// copies its closure prologue makes are guarded by a condition this test
/// never defines, and the prologues are [#error]s: anything that escapes the
/// guard stops the C compiler.  [main] reaches [fancy] only under an [if]
/// on a [custard_c_ifdef] flag with the same condition, and [helper]'s
/// original stays unguarded for the [#else] branch.
///
/// [always] is a flag whose condition holds, so that the [then] branch of a
/// preprocessor [if] is shown to run too.
///
/// [pick]'s [x], and the local [z], are read only in the arm this test
/// compiles out, so the arm it keeps voids them (issue 4758): -Werror is the
/// assertion.

[@@custard_c_ifdef "defined(CUSTARD_TEST_NO_SUCH_ARCH)"]
assume val fancy_arch : bool

[@@custard_c_ifdef "1"]
assume val always : bool

let deep (n : U32.t) : U32.t = U32.add_mod n 1ul
let helper (n : U32.t) : U32.t = deep n

[@@CPrologue "#error seed escaped its guard";
   custard_c_closure_prologue "#error copy escaped its guard";
   custard_c_closure_guard "defined(CUSTARD_TEST_NO_SUCH_ARCH)"]
let fancy (n : U32.t) : U32.t = U32.add_mod (helper n) 100ul

let pick (x y : U32.t) : U32.t =
  let z = U32.mul_mod y y in
  if fancy_arch then U32.add_mod x z else 0ul

let main () : ML I32.t =
  let a = if fancy_arch then fancy 1ul else helper (U32.add_mod 1ul (pick 3ul 4ul)) in
  let b = if always then U32.add_mod a 10ul else 0ul in
  if U32.eq b 12ul then 0l else 1l

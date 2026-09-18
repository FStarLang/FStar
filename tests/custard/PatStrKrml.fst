module PatStrKrml

module U32 = FStar.UInt32

/// Section 48.3.  The same match as [PatStr.classify], on the karamel
/// backend.
///
/// karamel's [pattern] cannot hold a string constant, and for two rounds this
/// was refused on that basis.  But that is a fact about karamel's *patterns*:
/// it compares strings properly, through [__eq__Prims_string], which krmllib
/// realizes as [strcmp (...) == 0].  So the match is desugared into the same
/// if-chain the direct C backend builds, and both backends now match on
/// strings.
///
/// Before section 44.1 this compiled to the constant 1: every constant pattern
/// became a fresh *variable* pattern, which matches everything, so the first
/// branch swallowed the scrutinee and the other two were dead.  The order
/// below would catch that again.

[@@custard_extern "custard_test_heap_copy"; custard_c_header "PatStrKrml_stubs.h"]
assume val heap_copy (s : string) : string

let classify (s : string) : U32.t =
  match s with
  | "a" -> 1ul
  | "b" -> 2ul
  | _ -> 3ul

/// A variable pattern in the catch-all position binds the scrutinee, which the
/// desugaring has already let-bound; the binding has to reach the body.
let tag (s : string) : U32.t =
  match s with
  | "x" -> 0ul
  | other -> if other = "y" then 1ul else 2ul

let main () : FStar.Int32.t =
  let ha = heap_copy "a" in
  let hb = heap_copy "b" in
  if not (U32.eq (classify ha) 1ul) then 1l
  else if not (U32.eq (classify hb) 2ul) then 2l
  else if not (U32.eq (classify (heap_copy "z")) 3ul) then 3l
  else if not (U32.eq (tag (heap_copy "x")) 0ul) then 4l
  else if not (U32.eq (tag (heap_copy "y")) 1ul) then 5l
  else if not (U32.eq (tag (heap_copy "q")) 2ul) then 6l
  else 0l

module ScrutCap
module U32 = FStar.UInt32

/// Section 50.1.  A source variable named [scrut].
///
/// Section 48.3's string-match desugaring let-binds the scrutinee under an
/// invented name, and invented the name by writing it down.  [find] takes the
/// first match, so the binder captured every reference to a *source* variable
/// of that name: the guard below read the scrutinee instead of the parameter,
/// karamel marked the parameter unused, and the program silently computed the
/// wrong answer.
///
/// [pick "yes" "a"] is 1.  Under the capture it was 9.

[@@custard_extern "custard_test_heap_copy"; custard_c_header "PatStrKrml_stubs.h"]
assume val heap_copy (s : string) : string

let pick (scrut : string) (s : string) : U32.t =
  match s with
  | "a" -> if scrut = "yes" then 1ul else 9ul
  | _   -> 3ul

/// And once more with the name shadowed a second time, so that the freshener
/// has to count rather than merely append: [scrut] and [scrut1] are both
/// taken, so the invented binder is [scrut2].
let pick2 (scrut : string) (scrut1 : string) (s : string) : U32.t =
  match s with
  | "a" -> if scrut = "yes" && scrut1 = "no" then 5ul else 9ul
  | _   -> 3ul

let main () : FStar.Int32.t =
  let a = heap_copy "a" in
  if not (U32.eq (pick (heap_copy "yes") a) 1ul) then 1l
  else if not (U32.eq (pick (heap_copy "no") a) 9ul) then 2l
  else if not (U32.eq (pick (heap_copy "yes") (heap_copy "z")) 3ul) then 3l
  else if not (U32.eq (pick2 (heap_copy "yes") (heap_copy "no") a) 5ul) then 4l
  else if not (U32.eq (pick2 (heap_copy "yes") (heap_copy "x") a) 9ul) then 5l
  else 0l

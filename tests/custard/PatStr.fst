module PatStr

module U32 = FStar.UInt32

/// Section 44.  Matching on a string constant, and comparing two strings.
///
/// Both were wrong, in different ways, in different backends.  The karamel
/// backend turned the constant patterns below into fresh *variable* patterns,
/// which match everything, so [classify] became the constant 1 and the two
/// branches after the first were dead.  The C backend emitted [s == "a"],
/// which compares addresses.
///
/// The second of those exits 0 if every string in the program is a literal,
/// because the C compiler pools literals and the addresses then agree by
/// accident.  [heap_copy] is here to defeat that: same contents, different
/// address.  A test that only ever compares literals is testing the pool.

[@@custard_extern "custard_test_heap_copy"; custard_c_header "PatStr_stubs.h"]
assume val heap_copy (s : string) : string

let classify (s : string) : U32.t =
  match s with
  | "a" -> 1ul
  | "b" -> 2ul
  | _ -> 3ul

let eq (a b : string) : bool = a = b

let neq (a b : string) : bool = a <> b

let main () : U32.t =
  let ha = heap_copy "a" in
  let hb = heap_copy "b" in
  if not (U32.eq (classify ha) 1ul) then 1ul
  else if not (U32.eq (classify hb) 2ul) then 2ul
  else if not (U32.eq (classify (heap_copy "z")) 3ul) then 3ul
  else if not (U32.eq (classify "a") 1ul) then 4ul
  else if not (eq ha "a") then 5ul
  else if eq ha hb then 6ul
  else if neq ha "a" then 7ul
  else if not (neq ha hb) then 8ul
  else 0ul

module ChrTy

module U32 = FStar.UInt32

/// Section 46.2.  A char in type position, and no character constant
/// anywhere.
///
/// The krml backend emitted an opaque [typedef struct FStar_Char_char_s
/// FStar_Char_char;] for the realized type [FStar.Char.char], against
/// krmllib's own [typedef uint32_t FStar_Char_char;] in
/// [include/krml/internal/types.h], which every generated header includes.
/// The unit did not compile -- and needed no constant to not compile, which
/// is why this test has none.

[@@custard_extern "custard_test_a_char"; custard_c_header "ChrTy_stubs.h"]
assume val a_char (_ : unit) : FStar.Char.char

let same (c : FStar.Char.char) : FStar.Char.char = c

let main () : FStar.Int32.t =
  if same (a_char ()) = a_char () then 0l else 1l

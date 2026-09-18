module ExtDup
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

/// Section 53.3.  Two externals sharing one [@@custard_extern] target name,
/// with different types.
///
/// This is exactly what Warning 367's own advice used to recommend for a C
/// target that accepts several type vectors -- and following it, alone, gives
/// a file that does not compile: one C symbol has one prototype.  The same
/// pair arises without any hand-writing under
/// [--custard_monomorphize_types], where a polymorphic external is
/// specialized at each type vector and every copy keeps the one target name.
///
/// The answer for a target that really does accept both is
/// [@@custard_c_header], which makes Custard emit no prototype at all and
/// include the real declaration instead.  That is the same mechanism a
/// variadic macro already needed, so there is one answer and not two.

[@@custard_extern "KCALL2"]
assume val kcall2_a : U32.t -> ML unit

[@@custard_extern "KCALL2"]
assume val kcall2_b : U64.t -> ML unit

let main () : ML I32.t =
  kcall2_a 1ul;
  kcall2_b 2uL;
  0l

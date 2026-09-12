module Template

open FStar.Attributes
module U32 = FStar.UInt32

/// Section 69.  An external type whose target spelling is a *template*.
///
/// The shape is the real one: `wmma::fragment<matrix_a, 16, 16, 16, half,
/// row_major>' needs three kinds of argument -- a tag that is a type in C++
/// but an index in F*, three sizes that are *values*, and an element type --
/// and Custard's `cty' had nowhere to put the sizes.  Before this, the only
/// way to write the type at all was `auto&' behind a typedef, which is not a
/// type a header can name and not one a struct can contain.
///
/// The tags need no new machinery: a nullary external type already prints its
/// target verbatim, so `matrix_a' is one.  The sizes are what `TConst' is
/// for.

[@@custard_extern "tpl_matrix_a"; custard_c_header "Template_stubs.h"]
assume val matrix_a : Type0

[@@custard_extern "tpl_matrix_b"; custard_c_header "Template_stubs.h"]
assume val matrix_b : Type0

[@@custard_extern "tpl_row_major"; custard_c_header "Template_stubs.h"]
assume val row_major : Type0

/// The placeholders count the declaration's binders from zero, in source
/// order, and a target may use them in any order and need not use them all.
[@@custard_extern "tpl_fragment({0}, {1}, {2}, {3}, {4}, {5})";
    custard_c_header "Template_stubs.h"]
assume val fragment (use : Type0) (m n k : nat) (t : Type0) (l : Type0) : Type0

/// [std::bitset<N>]: one value argument and nothing else.
[@@custard_extern "tpl_bitset({0})"; custard_c_header "Template_stubs.h"]
assume val bitset (n : nat) : Type0

[@@custard_extern "tpl_fill_a"; custard_c_header "Template_stubs.h"]
assume val fill_a (_ : unit)
  : FStar.All.ML (fragment matrix_a 16 16 16 U32.t row_major)

[@@custard_extern "tpl_fill_b"; custard_c_header "Template_stubs.h"]
assume val fill_b (_ : unit)
  : FStar.All.ML (fragment matrix_b 16 16 16 U32.t row_major)

[@@custard_extern "tpl_mma"; custard_c_header "Template_stubs.h"]
assume val mma (a : fragment matrix_a 16 16 16 U32.t row_major)
               (b : fragment matrix_b 16 16 16 U32.t row_major)
  : FStar.All.ML U32.t

[@@custard_extern "tpl_mask"; custard_c_header "Template_stubs.h"]
assume val mask (_ : unit) : FStar.All.ML (bitset 64)

[@@custard_extern "tpl_count"; custard_c_header "Template_stubs.h"]
assume val count (b : bitset 64) : FStar.All.ML U32.t

/// The point of getting the type into the IR rather than hiding it behind
/// [auto&]: it can be a local, a parameter and a return type, all named.
let step (_ : unit) : FStar.All.ML U32.t =
  let a = fill_a () in
  let b = fill_b () in
  mma a b

let main () : FStar.All.ML FStar.Int32.t =
  let s = step () in
  let c = count (mask ()) in
  if U32.eq s 6ul && U32.eq c 64ul then 0l else 1l

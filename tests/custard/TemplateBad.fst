module TemplateBad

open FStar.Attributes
module U32 = FStar.UInt32

/// Section 69.  A non-type template argument has to be a constant expression,
/// so an argument that is only known at run time is refused here rather than
/// pasted into a template-id the target's compiler would reject.

[@@custard_extern "tpl_bitset({0})"]
assume val bitset (n : nat) : Type0

[@@custard_extern "tpl_mask"]
assume val mask (n : nat) : FStar.All.ML (bitset n)

assume val width : nat

let main () : FStar.All.ML FStar.Int32.t =
  let _ = mask width in 0l

module TmplAbbrev

(* Section 74, the other half of the same defect.  The [Mono] binder [n] is
   behind the codomain abbreviation [use_t], so [specialize] never substituted
   the key into the body -- and [n] is also a *template argument* of the
   external type [bitset], which therefore reduced to a variable rather than
   to a constant and was refused with error 390.

   Kuiper's [Klas.GEMM.TensorCore2D.To] is this shape, over
   [wmma::fragment<..., FStar.SizeT.v tm, ...>]. *)

open FStar.Attributes
module U32 = FStar.UInt32

[@@custard_extern "tpl_bitset({0})"; custard_c_header "Template_stubs.h"]
assume val bitset (n : nat) : Type0

[@@custard_extern "tpl_mask"; custard_c_header "Template_stubs.h"]
assume val mask (_ : unit) : FStar.All.ML (bitset 64)

[@@custard_extern "tpl_count"; custard_c_header "Template_stubs.h"]
assume val count (b : bitset 64) : FStar.All.ML U32.t

inline_for_extraction noextract
let use_t = ([@@@monomorphize] n : nat) -> (b : bitset n) -> FStar.All.ML U32.t

let mk (bump : U32.t) : use_t = fun n b -> bump

let main () : FStar.All.ML FStar.Int32.t =
  let m = mask () in
  if U32.add_mod (mk 7ul 64 m) (count m) = 71ul then 0l else 1l

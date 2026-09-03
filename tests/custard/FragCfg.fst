module FragCfg

module G = FStar.Ghost
module U32 = FStar.UInt32

/// Section 47.2.  A configuration selected by a typeclass whose indices are
/// all erased, which is how the TensorCore fragment API is written.
///
/// The type is [custard_extern], and it is *indexed*.  Its C spelling is a
/// fixed string, so the indices are invisible to C and the arguments are
/// dropped on the way out; before that, an applied external type was
/// "Error 368: the polymorphic type FragCfg.frag has no C representation",
/// and the only way to write this was an unindexed external plus an
/// abbreviation carrying the indices.

unfold let en = G.erased nat
unfold let e16 : en = G.hide 16

type kind = | FragA | FragB | FragAcc

[@@custard_extern "fc_frag_t"; custard_c_header "FragCfg_stubs.h"]
assume val frag (knd : kind) (m n k : en) : Type0

inline_for_extraction noextract
class frag_cfg (knd : kind) (m n k : en) = {
  alloc : unit -> FStar.All.ML (frag knd m n k)
}

[@@custard_extern "fc_frag_a_16"; custard_c_header "FragCfg_stubs.h"]
assume val mk_a (_ : unit) : FStar.All.ML (frag FragA e16 e16 e16)

[@@custard_extern "fc_frag_b_16"; custard_c_header "FragCfg_stubs.h"]
assume val mk_b (_ : unit) : FStar.All.ML (frag FragB e16 e16 e16)

[@@custard_extern "fc_frag_acc_16"; custard_c_header "FragCfg_stubs.h"]
assume val mk_acc (_ : unit) : FStar.All.ML (frag FragAcc e16 e16 e16)

[@@custard_extern "fc_mma"; custard_c_header "FragCfg_stubs.h"]
assume val mma (#m #n #k : en)
  (c : frag FragAcc m n k) (a : frag FragA m n k) (b : frag FragB m n k)
  : FStar.All.ML U32.t

inline_for_extraction noextract
instance cfg_a : frag_cfg FragA e16 e16 e16 = { alloc = mk_a }
inline_for_extraction noextract
instance cfg_b : frag_cfg FragB e16 e16 e16 = { alloc = mk_b }
inline_for_extraction noextract
instance cfg_acc : frag_cfg FragAcc e16 e16 e16 = { alloc = mk_acc }

inline_for_extraction noextract
let step (#m #n #k : en)
  {| frag_cfg FragA m n k |} {| frag_cfg FragB m n k |} {| frag_cfg FragAcc m n k |}
  (_ : unit) : FStar.All.ML U32.t =
  let a : frag FragA m n k = alloc () in
  let b : frag FragB m n k = alloc () in
  let c : frag FragAcc m n k = alloc () in
  mma c a b

let kern (_ : unit) : FStar.All.ML U32.t = step #e16 #e16 #e16 ()

let main () : FStar.All.ML FStar.Int32.t =
  if U32.eq (kern ()) 6ul then 0l else 1l

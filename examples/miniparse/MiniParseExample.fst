module MiniParseExample
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics
module U8 = FStar.UInt8

#set-options "--no_smt"

let f : test -> Tot U8.t = T.synth_by_tactic (fun () -> gen_synth (`(test)))

let g : U8.t -> Tot test = T.synth_by_tactic (fun () -> invert_function (`(test)) (`(U8.t)) (`(op_Equality #U8.t)) (`(f)))

let test_bound : nat = T.synth_by_tactic (fun () -> tenum_bound (`(test)))

let f' : test -> Tot (bounded_u8 test_bound) = T.synth_by_tactic (fun () -> gen_synth_bounded (`(test)))

let g' : bounded_u8 test_bound -> Tot test = T.synth_by_tactic (fun () -> invert_function  (`(test)) (`(bounded_u8 test_bound)) (`(op_Equality #(bounded_u8 test_bound))) (`(f')))

let g'_inverse: squash (synth_inverse g' f') =
  T.synth_by_tactic synth_inverse_forall_tenum_solve

let g'_injective: squash (synth_inverse f' g') =
  T.synth_by_tactic synth_inverse_forall_bounded_u8_solve

let p = T.synth_by_tactic (fun () -> gen_enum_parser (`test))

let q = T.synth_by_tactic (fun () -> gen_parser32 (`p))

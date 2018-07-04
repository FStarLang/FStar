(* NOTE: This example MUST BE in an .fsti because of --use_extracted_interfaces *)

module MiniParse.Example
include MiniParse.Spec.TEnum

module T = FStar.Tactics
module U8 = FStar.UInt8

type test = | TA | TB | TC | TD

#set-options "--no_smt"

let f : test -> Tot U8.t = T.synth_by_tactic (fun () -> gen_synth (`(test)))

let g : U8.t -> Tot test = T.synth_by_tactic (fun () -> invert_function (`(test)) (`(U8.t)) (`(op_Equality #U8.t)) (`(f)))

let test_bound : nat = T.synth_by_tactic (fun () -> tenum_bound (`(test)))

let f' : test -> Tot (bounded_u8 test_bound) = T.synth_by_tactic (fun () -> gen_synth_bounded (`(test)))

let g' : bounded_u8 test_bound -> Tot test = T.synth_by_tactic (fun () -> invert_function  (`(test)) (`(bounded_u8 test_bound)) (`(op_Equality #(bounded_u8 test_bound))) (`(f')))

let g'_injective: squash (synth_injective g') =
  T.synth_by_tactic (fun () -> synth_injective_solve (`f'))

let g'_inverse: squash (synth_inverse g' f') =
  T.synth_by_tactic synth_inverse_solve

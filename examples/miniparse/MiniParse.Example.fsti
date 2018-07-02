module MiniParse.Example
include MiniParse.Spec.TEnum

module T = FStar.Tactics
module U8 = FStar.UInt8

type test = | TA | TB | TC | TD

#set-options "--no_smt"

let f : test -> Tot U8.t = T.synth_by_tactic (fun () -> gen_synth (`(test)))

let g : U8.t -> Tot test = T.synth_by_tactic (fun () -> invert_function (`(test)) (`(U8.t)) (`(op_Equality #U8.t)) (`(f)))

#reset-options

let test_bound : nat = T.synth_by_tactic (fun () -> tenum_bound (`(test)))

#set-options "--no_smt"

let f' : test -> Tot (bounded_u8 test_bound) = T.synth_by_tactic (fun () -> gen_synth_bounded (`(test)))

let g' : bounded_u8 test_bound -> Tot test = T.synth_by_tactic (fun () -> invert_function  (`(test)) (`(bounded_u8 test_bound)) (`(op_Equality #(bounded_u8 test_bound))) (`(f')))

module MiniParseExample
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

// #set-options "--no_smt"

#set-options "--z3rlimit 16"

let p = T.synth_by_tactic (fun () -> gen_enum_parser T.SMT (`test))

#set-options "--z3rlimit 32"

let q = T.synth_by_tactic (fun () -> gen_parser_impl T.SMT (`p))

#reset-options
 

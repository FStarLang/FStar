module __MODULE__
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

#reset-options "--z3rlimit 1 --z3rlimit_factor __FACTOR__ --z3seed __SEED__"
#set-options "--hint_info"
#set-options "--tactics_info"
#set-options "--log_queries"

let p__SUFFIX__ = T.synth_by_tactic (fun () -> gen_enum_parser T.__POLICY__ (`test))
let q__SUFFIX__ = T.synth_by_tactic (fun () -> gen_parser_impl T.__POLICY__)

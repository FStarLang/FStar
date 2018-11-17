module __MODULE__
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

#reset-options "--z3rlimit 1 --z3rlimit_factor __FACTOR__ --z3seed __SEED__ --max_fuel 0 --max_ifuel 0 --z3cliopt 'smt.qi.eager_threshold=1000' --query_stats --tactics_info"

let p__SUFFIX__ = T.synth_by_tactic (fun () -> gen_enum_parser T.__POLICY__ (`test))
let q__SUFFIX__ = T.synth_by_tactic (fun () -> gen_parser_impl T.__POLICY__)

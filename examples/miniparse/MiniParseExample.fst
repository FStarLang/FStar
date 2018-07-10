module MiniParseExample
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

#set-options "--no_smt"

let p = T.synth_by_tactic (fun () -> gen_enum_parser T.Goal (`test))

let q = T.synth_by_tactic (fun () -> gen_parser32 T.Goal (`p))

#reset-options

(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module MiniParseExample
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl

module T = FStar.Tactics

// #set-options "--no_smt"

#set-options "--z3rlimit 32"

let p = T.synth_by_tactic (fun () -> gen_enum_parser T.SMT (`test))

#push-options "--compat_pre_core 1"
let q = T.synth_by_tactic (fun () -> gen_parser_impl T.Goal)
#pop-options

//more goals show up with Core checking
let q' : parser_impl p = T.synth_by_tactic (fun () -> gen_parser_impl T.SMT)

#reset-options
 

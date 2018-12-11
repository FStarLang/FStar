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

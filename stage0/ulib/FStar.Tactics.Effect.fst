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
module FStar.Tactics.Effect

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Tactics.Types
open FStar.Stubs.Tactics.Result

/// This admit is to typecheck the bind implementation when the
///   interface is interleaved

#push-options "--admit_smt_queries true"
let tac_bind_interleave_begin = ()
#pop-options
let tac_bind_interleave_end = ()

let with_tactic _ p = p

let rewrite_with_tactic _ p = p

let synth_by_tactic #_ _ = admit ()

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
let assert_by_tactic _ _ = ()
#pop-options

let by_tactic_seman _ _ = ()

let preprocess_with _ = ()

let postprocess_with _ = ()

let postprocess_for_extraction_with _ = ()

#set-options "--no_tactics"

let unfold_with_tactic _ _ = ()

let unfold_rewrite_with_tactic _ _ = ()

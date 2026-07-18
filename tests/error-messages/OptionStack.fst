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
module OptionStack

assume val p : int -> prop

[@@expect_failure]
let t0 = assert (p 1)

[@@expect_failure]
let t1 = assert (p 2)

[@@expect_failure]
let t2 = assert False

#push-options "--admit_smt_queries true"

let t3 = assert False
let t4 = assert False
let t5 = assert False
let t6 = assert False

#pop-options

[@@expect_failure]
let t7 = assert False

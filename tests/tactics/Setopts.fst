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
module Setopts

open FStar.Tactics.V2
open FStar.Mul

let mult_ass (x y z : int) =
    assert ((x + x) * (y * z) = (x * y) * z + (z * x * y))
        by (set_options "--smtencoding.elim_box true --z3rlimit 1")

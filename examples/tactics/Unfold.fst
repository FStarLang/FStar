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
module Unfold

open FStar.Tactics

let x = 2
let y = x + x

let guard b =
    if not b
    then fail ("guard failed: " ^ term_to_string (quote b))

let _ = assert_by_tactic True
            (fun () -> guard (norm_term [delta_only [`%y]] (`y)  `term_eq` (`(x + x)));
                       guard (norm_term [delta_fully [`%y]] (`y) `term_eq` (`(2 + 2)));
                       ())

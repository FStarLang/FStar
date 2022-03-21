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
module BinaryTreesEnumeration

open FStar.List

let rec pairs_with_sum' m n =
  (m, n) ::
    (if m = 0
     then []
     else pairs_with_sum' (m - 1) (n + 1))

let rec pws'_complete (m d n: nat) :
  Lemma (List.memP (m, n + d) (pairs_with_sum' (m + d) n)) =
    if d = 0 then ()
    else begin
      assert (m + d <> 0);
      pws'_complete m (d - 1) (n + 1);
      assert (List.memP (m, (n + 1) + (d - 1)) (pairs_with_sum' (m + (d - 1)) (n + 1)));
      assert (List.memP (m, n + d) (pairs_with_sum' (m + d) n))
    end

(*> Why do I need to explicitly unfold [pairs_with_sum]? *)
let pws_complete (m n: nat) :
  Lemma (List.memP (m, n) (pairs_with_sum (m + n))) =
    assert (pairs_with_sum (m + n) == pairs_with_sum' (m + n) 0);
    pws'_complete m n 0

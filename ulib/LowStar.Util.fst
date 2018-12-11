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
module LowStar.Util
module HS = FStar.HyperStack
module B = LowStar.Buffer

let buf_t = a:Type & B.buffer a
let buf (#a:Type) (b:B.buffer a) : buf_t = (|a, b|)

unfold
let all_live (h:HS.mem) (l:list buf_t) : Type0 =
  BigOps.big_and #buf_t (fun (| _, b |) -> B.live h b) l

unfold
let all_disjoint (l:list B.loc) : Type0 =
  BigOps.pairwise_and B.loc_disjoint l

unfold
let loc_union_l (l:list B.loc) =
  BigOps.foldr_gtot l B.loc_union B.loc_none

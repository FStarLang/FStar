(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

let mods (l:hs_lens 'a 'b) (h:HS.mem) =
  B.modifies (as_loc l.footprint) l.snapshot h /\
  FStar.HyperStack.ST.equal_domains l.snapshot h

let inv #roots #view (l:hs_lens roots view) (h:HS.mem) =
  l.invariant l.x h /\
  mods l h

let view #roots #view (l:hs_lens roots view) (h:imem (inv l)) =
  l.l.get h

let reveal_inv ()
  : Lemma ((forall #a #b (l:hs_lens a b) h. {:pattern inv l h}
            inv l h <==>
            (l.invariant l.x h /\
             B.modifies (as_loc l.footprint) l.snapshot h /\
             FStar.HyperStack.ST.equal_domains l.snapshot h)) /\
           (forall #a #b (l:hs_lens a b) h. {:pattern view l h}
             view l h == l.l.get h))
  = ()

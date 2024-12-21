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
module FStar.MRef
open FStar.Heap
open FStar.ST

open FStar.Preorder

private let p_pred (#a:Type) (#b:preorder a) (r:mref a b) (p:(a -> Type))
  = fun h -> h `contains` r /\ p (sel h r)

let token #_ #_ r p = witnessed (p_pred r p)

let witness_token #_ #_ m p =
  gst_recall (contains_pred m);
  gst_witness (p_pred m p)

let recall_token #_ #_ m p = gst_recall (p_pred m p)

let lemma_functoriality #_ #_ r p q = lemma_functoriality (p_pred r p) (p_pred r q)

let recall p = gst_recall p

let witness p = gst_witness p

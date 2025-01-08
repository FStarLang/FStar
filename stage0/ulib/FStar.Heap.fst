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
module FStar.Heap

include FStar.Monotonic.Heap

let trivial_rel (a:Type0) :Preorder.relation a = fun x y -> True

let trivial_preorder (a:Type0) :Preorder.preorder a = trivial_rel a

type ref (a:Type0) = mref a (trivial_preorder a)

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
module Bug1065a

assume type mem

let st_pre = st_pre_h mem
let st_post' (a:Type) (pre:Type) = st_post_h' mem a pre

assume val myStack : (a:Type) -> (pre:st_pre) -> (post: (m0:mem -> Tot (st_post' a (pre m0)))) -> Type0

assume val gg : #a:Type -> #pre:(st_pre_h mem) -> #post:(mem -> Tot (st_post_h' mem a True)) -> myStack a pre post

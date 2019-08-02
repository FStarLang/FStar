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
module Unit1.RefinementInference
assume type erased : Type -> Type
assume val reveal: erased 'a -> GTot 'a
assume val consHd : #a:Type -> l:list a{Cons? l} -> Tot a
assume val elift1_p : #a:Type -> #b:Type -> #p:(a -> GTot Type) -> 
		      $f:(x:a{p x} -> Tot b) -> 
		      r:erased a{p (reveal r) } -> 
		      Tot (erased b)

val ghostConsHd : a:Type -> l:erased (list a){Cons? (reveal l)} -> Tot (erased a)
let ghostConsHd (a:Type) l = elift1_p consHd l

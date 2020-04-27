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
module Sub2

assume val mem : 'a -> list 'a -> Tot bool

val xxx : list 'a -> Tot (l:list 'a{forall (x : 'a). mem x l ==> False})
let xxx l = l

(* Shouldn't print b2t
Error typing-error-subtyping2.fst(6,0-17,0): The following problems were found:
	Subtyping check failed; expected type l:(list 'a){(forall x:'a. (b2t (mem  x l)) ==> False)}; got type (list 'a) (typing-error-subtyping2.fst(6,12-6,13))
*)

(* This one requires reduction below a quantifier
Subtyping check failed; expected type
[Before:l:(list 'a){(Forall #'a (fun x:'a => (l_imp (b2t (mem #'a x l)) False)))}]
[After:l:(list 'a){(forall x:'a. (b2t (mem #'a x l)) ==> False)}];
got type
[Before:((fun 'a:Type => (list 'a)) 'a)]
[After:(list 'a)]
(typing-error.fst(6,12-6,13))
*)

(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.ErasedLogic

(*F* 's exists should be thought of Coq's sigT. It is totally unerased *)
(*Coq has 2 more versions, with increasing degree of erasure*)
(* https://coq.inria.fr/library/Coq.Init.Specif.html#sigT *)
open FStar.Ghost

(*you can get the witness x, that the proof part is erased*)
(*https://coq.inria.fr/library/Coq.Init.Specif.html#sig*)
type sig_ (a:Type) (p: a->Type) = exists (x:a). (erased (p x))


(*you get nothing. Of course, in ghost contexts, or to build other erased date, you get everything*)
(* https://coq.inria.fr/library/Coq.Init.Logic.html#ex *)
type ex (a:Type) (p:a->Type) = erased (exists (x:a). (p x))


(*how to use the above:*)
(*assuming that existentials in F* are constructive. If so, the following 2 assumes must be definable*)
assume val exists_proj1 : #a:Type -> #p:(a->Type) -> (exists x.p x) -> GTot a
assume val mkexists : #a:Type -> #p:(a->Type) -> x:a -> (p x) -> Tot (exists x.p x)


val ex_proj1 : #a:Type -> #p:(a->Type) -> ex a p -> Tot (erased a)
let ex_proj1 #a #p e = (elift1 (exists_proj1 #a #p)) e


val gex_proj1 : #a:Type -> #p:(a->Type) -> (ex a p) -> GTot a
let gex_proj1 #a #p e = (reveal (ex_proj1 e))

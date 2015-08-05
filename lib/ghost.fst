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
(*
  This module provides a ghost type,
  to abstract computationally irrelevant values.

  It relies on the GHOST effect defined in Prims
*)
module Ghost
private type erased (a:Type) = a
val reveal: #a:Type -> erased a -> GTot a
let reveal x = x

val hide: #a:Type -> a -> Tot (erased a)
let hide x = x

val lemma_hide_reveal: #a:Type
                   -> x:erased a
                   -> Lemma (ensures (hide (reveal x) = x))
let lemma_hide_reveal x = ()

val as_ghost: #a:Type
          -> f:(unit -> Tot a)
          -> Pure (erased a)
                  (requires True)
                  (ensures (fun x -> reveal x = f ()))
let as_ghost f = f ()

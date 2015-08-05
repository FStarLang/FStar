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

(*just hide can do this now. remove?*)
val as_ghost: #a:Type
          -> f:(unit -> Tot a)
          -> Pure (erased a)
                  (requires True)
                  (ensures (fun x -> reveal x = f ()))
let as_ghost f = f ()

(*Just like Coq's prop, it is okay to use erased types freely as long as we produce an erased type*)
val elift1 : #a:Type -> #b:Type -> f:(a->Tot b) -> erased a -> Tot (erased b)
let elift1 f ga = f ga

val elift2 : #a:Type -> #b:Type -> #c:Type  -> f:(a-> c ->Tot b) -> erased a -> erased c -> Tot (erased b)
let elift2 f ga gc = f ga gc

val elift3 : #a:Type -> #b:Type -> #c:Type-> #d:Type  -> f:(a-> c -> d ->Tot b) -> erased a -> erased c ->  erased d -> Tot (erased b)
let elift3 f ga gc gd = f ga gc gd

(*
Privateness seems to have no effect on Z3. So perhaps we dont need any postconditions

val elift1 : #a:Type -> #b:Type -> f:(a->Tot b) -> ga:(erased a) -> Pure (erased b) (requires True) (ensures (fun x -> reveal x = f ga))
let elift1 f ga = f ga

val elift2 : #a:Type -> #b:Type -> #c:Type  -> f:(a-> c ->Tot b) -> ga:(erased a) -> gc:(erased c) -> Pure (erased b) (requires True) (ensures (fun x -> reveal x = f ga gc))
let elift2 f ga gc = f ga gc

val elift3 : #a:Type -> #b:Type -> #c:Type-> #d:Type  -> f:(a-> c -> d ->Tot b) -> ga:(erased a) -> gc:(erased c) ->  gd:(erased d)
-> Pure (erased b) (requires True) (ensures (fun x -> reveal x = f ga gc gd))
let elift3 f ga gc gd = f ga gc gd
*)

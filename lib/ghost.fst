(*--build-config
  --*)

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

module FStar.Ghost
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

val elift1_p : #a:Type -> #b:Type -> #p:(a->Type) -> =f:(x:a{p x} ->Tot b) -> r:(erased a){p (reveal r) } -> Tot (erased b)
let elift1_p f ga = f ga

val elift2_p : #a:Type  -> #c:Type -> #p:(a->c->Type) -> #b:Type -> f:(xa:a-> xc:c{p xa xc} ->Tot b)
  -> ra:(erased a) -> rc:(erased c){p (reveal ra) (reveal rc)}  -> Pure (erased b) (requires True) (ensures (fun x -> reveal x = f ra rc))
let elift2_p f ga gc = f ga gc

(*
val elift2_wp : #a:Type  -> #c:Type  -> #b:Type -> #pre:(a->c->Type) -> #post:(a->c->b->Type)
-> f:(ra:a -> rc:c ->Pure b (requires (pre ra rc)) (ensures (fun rb -> post ra rc rb)))
  -> ra:(erased a) -> rc:(erased c)  ->
    Pure (erased b)
            (requires (pre (reveal ra) (reveal rc)))
            (requires (fun rb -> post (reveal ra) (reveal rc) (reveal rb)))
let elift2_wp f ga gc = f ga gc

(*perhaps replace elift1_p with this*)
val elift1_pd : #a:Type -> #b:(a->Type) -> #p:(a->Type) -> f:(x:a->Tot (b x)) -> r:(erased a){p (reveal r)} -> Tot (erased (b (reveal r)))
let elift1_pd f ga = f ga
*)

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

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

abstract
type erased (a:Type) = a

abstract
let reveal (#a:Type) (x:erased a) : GTot a = x

abstract
let hide (#a:Type) (x:a) : Tot (erased a) = x

//reveal is injective
//hide is its inverse
val lemma_hide_reveal: #a:Type
                   -> x:erased a
                   -> Lemma (ensures (hide (reveal x) == x))
                           [SMTPat (reveal x)]
let lemma_hide_reveal #a x = ()

val lemma_reveal_hide: #a:Type
                   -> x:a
                   -> Lemma (ensures (reveal (hide x) == x))
                           [SMTPat (hide x)]
let lemma_reveal_hide #a x = ()

(*Just like Coq's prop, it is okay to use erased types freely as long as we produce an erased type*)
val elift1 : #a:Type -> #b:Type -> f:(a->GTot b) -> x:erased a -> Tot (y:erased b{reveal y == f (reveal x)})
let elift1 #a #b f ga = f ga

val elift2 : #a:Type -> #b:Type -> #c:Type  -> f:(a-> c ->GTot b) -> ga:erased a -> gc:erased c -> Tot (e:erased b{reveal e == f (reveal ga) (reveal gc)})
let elift2 #a #b #c f ga gc = f ga gc

val elift3 : #a:Type -> #b:Type -> #c:Type-> #d:Type  -> f:(a-> c -> d ->GTot b) -> ga:erased a -> gc:erased c ->  gd:erased d -> Tot (e:erased b{reveal e == f (reveal ga) (reveal gc) (reveal gd)})
let elift3 #a #b #c #d f ga gc gd = f ga gc gd

val elift1_p : #a:Type -> #b:Type -> #p:(a->Type) -> $f:(x:a{p x} ->GTot b) -> r:erased a{p (reveal r) } -> Tot (z:erased b{reveal z == f (reveal r)})
let elift1_p #a #b #p f ga = f ga

val elift2_p : #a:Type  -> #c:Type -> #p:(a->c->Type) -> #b:Type -> f:(xa:a-> xc:c{p xa xc} ->GTot b)
  -> ra:(erased a) -> rc:(erased c){p (reveal ra) (reveal rc)}  -> Pure (erased b) (requires True) (ensures (fun x -> reveal x == f ra rc))
let elift2_p #a #c #p #b f ga gc = f ga gc

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

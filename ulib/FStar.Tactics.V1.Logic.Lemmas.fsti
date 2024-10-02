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
module FStar.Tactics.V1.Logic.Lemmas

val fa_intro_lem (#a:Type) (#p:a -> Type) (f:(x:a -> squash (p x))) : Lemma (forall (x:a). p x)

val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
val imp_intro_lem : (#a:Type) -> (#b : Type) ->
                            (a -> squash b) ->
                            Lemma (a ==> b)
val __lemma_to_squash #req #ens (_ : squash req) (h : (unit -> Lemma (requires req) (ensures ens))) : squash ens

val vbind : (#p:Type) -> (#q:Type) -> squash p -> (p -> squash q) -> Lemma q

val or_ind : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                     (p \/ q) ->
                     (squash (p ==> phi)) ->
                     (squash (q ==> phi)) ->
                     Lemma phi

val bool_ind : (b:bool) -> (phi:Type) -> (squash (b == true  ==> phi)) ->
                                                 (squash (b == false ==> phi)) ->
                                                 Lemma phi

val or_intro_1 : (#p:Type) -> (#q:Type) -> squash p -> Lemma (p \/ q)

val or_intro_2 : (#p:Type) -> (#q:Type) -> squash q -> Lemma (p \/ q)

val __and_elim : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi

val __and_elim' : (#p:Type) -> (#q:Type) -> (#phi:Type) ->
                              squash (p /\ q) ->
                              squash (p ==> q ==> phi) ->
                              Lemma phi

val __witness : (#a:Type) -> (x:a) -> (#p:(a -> Type)) -> squash (p x) -> squash (exists (x:a). p x)

val __elim_exists' #t (#pred : t -> Type0) #goal (h : (exists x. pred x))
                          (k : (x:t -> pred x -> squash goal)) : squash goal

val __forall_inst #t (#pred : t -> Type0) (h : (forall x. pred x)) (x : t) : squash (pred x)

val __forall_inst_sq #t (#pred : t -> Type0) (h : squash (forall x. pred x)) (x : t) : squash (pred x)

val sklem0 (#a:Type) (#p : a -> Type0) ($v : (exists (x:a). p x)) (phi:Type0) :
  Lemma (requires (forall x. p x ==> phi))
        (ensures phi)

val lemma_from_squash : #a:Type -> #b:(a -> Type) -> (x:a -> squash (b x)) -> x:a -> Lemma (b x)

val lem1_fa #a #pre #post
  ($lem : (x:a -> Lemma (requires pre x) (ensures post x))) :
  Lemma (forall (x:a). pre x ==> post x)

val lem2_fa #a #b #pre #post
  ($lem : (x:a -> y:b -> Lemma (requires pre x y) (ensures post x y))) :
  Lemma (forall (x:a) (y:b). pre x y ==> post x y)

val lem3_fa #a #b #c #pre #post
  ($lem : (x:a -> y:b -> z:c -> Lemma (requires pre x y z) (ensures post x y z))) :
  Lemma (forall (x:a) (y:b) (z:c). pre x y z ==> post x y z)

val revert_squash : (#a:Type) -> (#b : (a -> Type)) ->
                            (squash (forall (x:a). b x)) ->
                            x:a -> squash (b x)

(*
   Copyright 2020 Microsoft Research

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

module Steel.PCM

let symrel a = c:(a -> a -> prop) { (forall x y. c x y <==> c y x) }

noeq
type pcm' (a:Type) = {
  composable: symrel a;
  op: x:a -> y:a{composable x y} -> a;
  one:a
}

let lem_commutative #a (p:pcm' a) =
  x:a ->
  y:a{p.composable x y} ->
  Lemma (p.op x y == p.op y x)

let lem_assoc_l #a (p:pcm' a) =
  x:a ->
  y:a ->
  z:a{p.composable y z /\ p.composable x (p.op y z)} ->
  Lemma (p.composable x y /\
         p.composable (p.op x y) z /\
         p.op x (p.op y z) == p.op (p.op x y) z)

let lem_assoc_r #a (p:pcm' a) =
  x:a ->
  y:a ->
  z:a {p.composable x y /\
       p.composable (p.op x y) z} ->
  Lemma
      (p.composable y z /\
       p.composable x (p.op y z) /\
       p.op x (p.op y z) == p.op (p.op x y) z)


let lem_is_unit #a (p:pcm' a) =
  x:a ->
  Lemma (p.composable x p.one /\
         p.op x p.one == x)

noeq
type pcm (a:Type) = {
  p:pcm' a;
  comm:lem_commutative p;
  assoc: lem_assoc_l p;
  assoc_r: lem_assoc_r p;
  is_unit: lem_is_unit p
}

let composable #a (p:pcm a) (x y:a) = p.p.composable x y
let op #a (p:pcm a) (x:a) (y:a{composable p x y}) = p.p.op x y
let compatible #a (pcm:pcm a) (x y:a) =
  (exists (frame:a). composable pcm x frame /\
                op pcm frame x == y)

let compatible_refl #a (pcm:pcm a) (x:a)
  : Lemma (compatible pcm x x)
  = pcm.is_unit x;
    pcm.comm x pcm.p.one;
    assert (op pcm pcm.p.one x == x)

let frame_preserving #a (pcm:pcm a) (x y: a) =
    (forall frame. composable pcm frame x ==> composable pcm frame y) /\
    (forall frame.{:pattern (composable pcm frame x)} composable pcm frame x ==> op pcm frame y == y)

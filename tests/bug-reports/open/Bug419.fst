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
module Bug419

type rel (v: Type) = v -> v -> Type
noeq type path (v: Type) (r: v -> v -> Type): v -> v -> Type =
  | Refl: x:v -> path v r x x
  | Step: x:v -> y:v -> z:v -> r x y -> path v r y z -> path v r x z

type is_root (v: Type) (f: rel v) (x: v) =
  forall y. ~(f x y)
type is_repr (v: Type) (f: rel v) (x: v) (r: v) =
  path v f x r /\ is_root v f r

type confined (v: eqtype) (d: Set.set v) (f: rel v) =
  forall (x: v) (y: v). path v f x y ==> Set.mem x d /\ Set.mem y d
type functional (v: eqtype) (f: rel v) =
  forall (x: v) (y: v) (z: v). f x z /\ f y z ==> x = y
type defined (v: eqtype) (rel: rel v) =
  forall (x: v). exists (r: v). rel x r

type is_dsf (v: eqtype) (d: Set.set v) (f: rel v) =
  confined v d f /\ functional v f /\ defined v (is_repr v f)

val path_same_repr:
  v:eqtype -> d:Set.set v -> f:rel v ->
  x:v -> r:v -> z:v -> p_1:path v f x z -> p_2:path v f x r -> Lemma
    (requires (is_dsf v d f /\ is_root v f r))
    (ensures (is_repr v f z r))
    (decreases %[p_1, p_2])
let rec path_same_repr (v: eqtype) d (f: rel v) x r z p_1 p_2 =
  match p_1, p_2 with
  | Refl _, Refl _ ->
    admit ()

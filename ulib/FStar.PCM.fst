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
module FStar.PCM

/// This module defines the partial commutative monoid (PCM) algebraic structure, as well as helper
/// predicates and functions to manipulate PCMs.

(**** Base definitions *)

(** A symmetric relation *)
let symrel (a: Type u#a) = c:(a -> a -> prop) { (forall x y. c x y <==> c y x) }

(** [pcm'] is a magma, the base for the partial commutative monoid *)
noeq
type pcm' (a:Type u#a) = {
  composable: symrel a;
  op: x:a -> y:a{composable x y} -> a;
  one:a
}

(** The type of a commutativity property *)
let lem_commutative (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a{p.composable x y} ->
    Lemma (p.op x y == p.op y x)

(** The type of a left-associativity property *)
let lem_assoc_l (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a ->
  z:a{p.composable y z /\ p.composable x (p.op y z)} ->
  Lemma (p.composable x y /\
         p.composable (p.op x y) z /\
         p.op x (p.op y z) == p.op (p.op x y) z)


(** The type of a right-associativity property *)
let lem_assoc_r (#a: Type u#a) (p:pcm' a) =
  x:a ->
  y:a ->
  z:a {p.composable x y /\
       p.composable (p.op x y) z} ->
  Lemma
      (p.composable y z /\
       p.composable x (p.op y z) /\
       p.op x (p.op y z) == p.op (p.op x y) z)

(** The type of the property characterizing the unit element of the monoid *)
let lem_is_unit (#a: Type u#a) (p:pcm' a) =
  x:a ->
  Lemma (p.composable x p.one /\
         p.op x p.one == x)

(** Main type describing partial commutative monoids *)
noeq
type pcm (a:Type u#a) = {
  p:pcm' a;
  comm:lem_commutative p;
  assoc: lem_assoc_l p;
  assoc_r: lem_assoc_r p;
  is_unit: lem_is_unit p;
  refine: a -> prop
}

(**** Derived predicates *)


(** Returns the composable predicate of the PCM *)
let composable (#a: Type u#a) (p:pcm a) (x y:a) = p.p.composable x y

(** Calls the operation of the PCM *)
let op (#a: Type u#a) (p:pcm a) (x:a) (y:a{composable p x y}) = p.p.op x y

(**
  Two elements [x] and [y] are compatible with respect to a PCM if their subtraction
  is well-defined, e.g. if there exists an element [frame] such that [x * z = y]
*)
let compatible (#a: Type u#a) (pcm:pcm a) (x y:a) =
  (exists (frame:a).
    composable pcm x frame /\ op pcm frame x == y
  )

(** Compatibility is reflexive *)
let compatible_refl
  (#a: Type u#a) (pcm:pcm a) (x:a)
    : Lemma (compatible pcm x x)
  =
  pcm.is_unit x;
  pcm.comm x pcm.p.one;
  assert (op pcm pcm.p.one x == x)

(** Compatibility is transitive *)
let compatible_trans
  (#a: Type u#a) (pcm:pcm a) (x y z:a)
  : Lemma (requires (compatible pcm x y /\ compatible pcm y z))
          (ensures (compatible pcm x z))
  = Classical.forall_intro_3 pcm.assoc

(**
  Helper function to get access to the existentially quantified frame between two compatible
  elements
*)
let compatible_elim
  (#a: Type u#a) (pcm:pcm a) (x y:a)
  (goal: Type)
  (lemma: (frame: a{composable pcm x frame /\ op pcm frame x == y}) ->
    Lemma (goal)
  )
    : Lemma (requires (compatible pcm x y)) (ensures (goal))
  =
  Classical.exists_elim
    goal #a #(fun frame -> composable pcm x frame /\ op pcm frame x == y)
    () (fun frame -> lemma frame)
    
let compatible_intro
  (#a: Type u#a) (pcm:pcm a) (x y:a)
  (frame: a)
  : Lemma
    (requires (composable pcm x frame /\ op pcm frame x == y))
    (ensures (compatible pcm x y))
  = ()

(** Two elements are joinable when they can evolve to a common point. *)
let joinable #a (p:pcm a) (x y : a) : prop =
  exists z. compatible p x z /\ compatible p y z

let frame_compatible #a (p:pcm a) (x:FStar.Ghost.erased a) (v y:a) =
  (forall (frame:a). {:pattern (composable p x frame)}
            composable p x frame /\
            v == op p x frame ==>
            composable p y frame /\
            v == op p y frame)

(*
 * Frame preserving updates from x to y
 *   - should preserve all frames,
 *   - and a frame containing rest of the PCM value should continue to do so
 *)

type frame_preserving_upd (#a:Type u#a) (p:pcm a) (x y:a) =
  v:a{
    p.refine v /\
    compatible p x v
  } ->
  v_new:a{
    p.refine v_new /\
    compatible p y v_new /\
    (forall (frame:a{composable p x frame}).{:pattern composable p x frame}
       composable p y frame /\
       (op p x frame == v ==> op p y frame == v_new))}


(*
 * A specific case of frame preserving updates when y is a refined value
 *
 * All the frames of x should compose with--and the composition should result in--y
 *)
let frame_preserving (#a: Type u#a) (pcm:pcm a) (x y: a) =
    (forall frame. composable pcm frame x ==> composable pcm frame y) /\
    (forall frame.{:pattern (composable pcm frame x)} composable pcm frame x ==> op pcm frame y == y)

(*
 * As expected, given frame_preserving, we can construct a frame_preserving_update
 *)
let frame_preserving_val_to_fp_upd (#a:Type u#a) (p:pcm a)
  (x:Ghost.erased a) (v:a{frame_preserving p x v /\ p.refine v})
  : frame_preserving_upd p x v
  = Classical.forall_intro (p.comm v);
    fun _ -> v

(** The PCM [p] is exclusive to element [x] if the only element composable with [x] is [p.one] *)
let exclusive (#a:Type u#a) (p:pcm a) (x:a) =
  forall (frame:a). composable p x frame ==> frame == p.p.one

(** A mutation from [x] to [p.one] is frame preserving if [p] is exclusive to [x] *)
let exclusive_is_frame_preserving (#a: Type u#a) (p:pcm a) (x:a)
  : Lemma (requires exclusive p x)
          (ensures frame_preserving p x p.p.one)
  = p.is_unit x;
    p.is_unit p.p.one

(* Some sanity checks on the definition of frame preserving updates *)

let no_op_is_frame_preserving (#a:Type u#a) (p:pcm a)
  (x:a)
  : frame_preserving_upd p x x
  = fun v -> v

let compose_frame_preserving_updates (#a:Type u#a) (p:pcm a)
  (x y z:a)
  (f:frame_preserving_upd p x y)
  (g:frame_preserving_upd p y z)
  : frame_preserving_upd p x z
  = fun v -> g (f v)

let frame_preserving_subframe (#a:Type u#a) (p:pcm a) (x y:a)
  (subframe:a{composable p x subframe /\ composable p y subframe})
  (f:frame_preserving_upd p x y)
  : frame_preserving_upd p (op p x subframe) (op p y subframe)
  = fun v ->
    compatible_elim p (op p x subframe) v (compatible p x v) (fun frame ->
      p.comm x subframe;
      p.assoc frame subframe x);
    let w = f v in
    let aux (frame: a{composable p (op p x subframe) frame}):
      Lemma (composable p (op p y subframe) frame /\
             (op p (op p x subframe) frame == v ==> op p (op p y subframe) frame == w))
             [SMTPat (composable p (op p y subframe) frame)]
    = p.assoc_r x subframe frame;
      assert (composable p x (op p subframe frame));
      assert (composable p y (op p subframe frame));
      p.assoc y subframe frame
    in
    compatible_elim p (op p x subframe) v (compatible p (op p y subframe) w) (fun frame ->
      aux frame;
      p.comm frame (op p x subframe);
      p.comm (op p y subframe) frame);
    w


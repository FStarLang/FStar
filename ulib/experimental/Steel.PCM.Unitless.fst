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

module Steel.PCM.Unitless

open Steel.PCM

noeq type unitless_pcm' (a: Type) = {
  unitless_composable: symrel a;
  unitless_op: x:a -> y:a{unitless_composable x y} -> a;
}

let unitless_lem_commutative #a (p:unitless_pcm' a) =
  x:a ->
  y:a{p.unitless_composable x y} ->
  Lemma (p.unitless_op x y == p.unitless_op y x)

let unitless_lem_assoc_l #a (p:unitless_pcm' a) =
  x:a ->
  y:a ->
  z:a{p.unitless_composable y z /\ p.unitless_composable x (p.unitless_op y z)} ->
  Lemma (p.unitless_composable x y /\
         p.unitless_composable (p.unitless_op x y) z /\
         p.unitless_op x (p.unitless_op y z) == p.unitless_op (p.unitless_op x y) z)

let unitless_lem_assoc_r #a (p:unitless_pcm' a) =
  x:a ->
  y:a ->
  z:a {p.unitless_composable x y /\
       p.unitless_composable (p.unitless_op x y) z} ->
  Lemma
      (p.unitless_composable y z /\
       p.unitless_composable x (p.unitless_op y z) /\
       p.unitless_op x (p.unitless_op y z) == p.unitless_op (p.unitless_op x y) z)


noeq type unitless_pcm (a: Type) = {
  unitless_p: unitless_pcm' a;
  unitless_comm:unitless_lem_commutative unitless_p;
  unitless_assoc: unitless_lem_assoc_l unitless_p;
  unitless_assoc_r: unitless_lem_assoc_r unitless_p;
}

let add_unit_to_pcm
  (#a: Type)
  (p: unitless_pcm a)
  (one: a)
  (is_unit: (
    x:a ->
    Lemma (p.unitless_p.unitless_composable x one /\
         p.unitless_p.unitless_op x one == x)
  ))
    : pcm a
  =
  let pcm' : pcm' a = {
    composable = p.unitless_p.unitless_composable;
    op = p.unitless_p.unitless_op;
    one = one
    }
  in
  {
    p = pcm';
    comm = p.unitless_comm;
    assoc = p.unitless_assoc;
    assoc_r = p.unitless_assoc_r;
    is_unit = is_unit;
  }

let to_full_pcm_with_unit
  (#a: Type)
  (p: unitless_pcm a)
  : pcm (option a)
  =
  let composable : symrel (option a) = fun x y ->
    match x, y with
    | Some x, Some y -> x `p.unitless_p.unitless_composable` y
    | _ -> True
  in
  let compose (x: option a) (y: option a{x `composable` y}) : option a =
    match x, y with
    | Some x, Some y -> Some (x `p.unitless_p.unitless_op` y)
    | Some x, None -> Some x
    | None, Some y -> Some y
    | None, None -> None
  in
  let one = None in
  let pcm' = {
    composable;
    op = compose;
    one
  } in
  {
    p = pcm';
    comm = (fun x y ->
      match x, y with
      | Some x, Some y -> p.unitless_comm x y
      | _ -> ()
    );
    assoc = (fun x y z ->
      match x, y, z with
      | Some x, Some y, Some z -> p.unitless_assoc x y z
      | _ -> ()
    );
    assoc_r = (fun x y z ->
       match x, y, z with
      | Some x, Some y, Some z -> p.unitless_assoc_r x y z
      | _ -> ()
    );
    is_unit = (fun _ -> ())
  }

(**
  Two elements [x] and [y] are compatible with respect to a PCM if their substraction
  is well-defined, e.g. if there exists an element [frame] such that [x * z = y]
*)
let compatible (#a: Type u#a) (pcm:unitless_pcm a) (x y:a) =
  (exists (frame:a).
    pcm.unitless_p.unitless_composable x frame /\ pcm.unitless_p.unitless_op frame x == y
  )

(**
  Helper function to get access to the existentially quantified frame between two compatible
  elements
*)
let compatible_elim
  (#a: Type u#a) (pcm:unitless_pcm a) (x y:a)
  (goal: Type)
  (lemma: (frame: a{
      pcm.unitless_p.unitless_composable x frame /\ pcm.unitless_p.unitless_op frame x == y
    }) ->
    Lemma (goal)
  )
    : Lemma (requires (compatible pcm x y)) (ensures (goal))
  =
  Classical.exists_elim
    goal #a #(fun frame ->
      pcm.unitless_p.unitless_composable x frame /\ pcm.unitless_p.unitless_op frame x == y
    ) () (fun frame -> lemma frame)

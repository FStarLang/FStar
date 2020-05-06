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
module Steel.PCM.Unitless.Base

open Steel.PCM
open Steel.PCM.Unitless

let composable_unitless_exclusive' (#a: Type u#a) (x y: a) : prop =
  False

let composable_unitless_exclusive (#a: Type u#a) : symrel a =
  fun (x y: a) -> composable_unitless_exclusive' x y

let compose_unitless_exclusive
  (#a: Type u#a)
  (x: a)
  (y: a{x `composable_unitless_exclusive` y}) =
  x

let exclusive_unitless_pcm' (#a: Type u#a) : unitless_pcm' a = {
  unitless_composable = composable_unitless_exclusive;
  unitless_op = compose_unitless_exclusive
}

let exclusive_unitless_pcm (#a: Type u#a) : unitless_pcm a = {
  unitless_p = exclusive_unitless_pcm';
  unitless_comm = (fun _ _ -> ());
  unitless_assoc = (fun _ _ _ -> ());
  unitless_assoc_r = (fun _ _ _ -> ())
}

let composable_unitless_immutable' (#a: Type u#a) (x y: a) : prop =
   x == y

let composable_unitless_immutable (#a: Type u#a) : symrel a =
  fun (x y: a) -> composable_unitless_immutable' x y


let compose_unitless_immutable
  (#a: Type u#a)
  (x: a)
  (y: a{x `composable_unitless_immutable` y}) : a  =
  x

let immutable_unitless_pcm' (#a: Type u#a) : unitless_pcm' a = {
  unitless_composable = composable_unitless_immutable;
  unitless_op = compose_unitless_immutable;
}

let immutable_unitless_pcm (#a: Type u#a) : unitless_pcm a = {
  unitless_p = immutable_unitless_pcm';
  unitless_comm = (fun _ _ -> ());
  unitless_assoc = (fun _ _ _ -> ());
  unitless_assoc_r = (fun _ _ _ -> ());
}

module Univ = FStar.Universe

let unit_pcm' : unitless_pcm' u#a (Univ.raise_t u#0 u#a unit) = {
    unitless_composable = (fun _ _ -> True);
    unitless_op = (fun _ _ -> Univ.raise_val u#0 u#a () )
  }

let unit_pcm : unitless_pcm u#a (Univ.raise_t u#0 u#a unit)  = {
  unitless_p = unit_pcm' u#a;
  unitless_comm = (fun _ _  -> ());
  unitless_assoc = (fun _ _ _ -> ());
  unitless_assoc_r = (fun _ _ _ -> ())
}

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
module Steel.PCM.Base

open Steel.PCM

let composable_exclusive' (#a: Type u#a) (x y: option a) : prop =
  match x,y with
  | Some _, Some _ -> False
  | _ -> True

let composable_exclusive (#a: Type u#a) : symrel (option a) =
  fun (x y: (option a)) -> composable_exclusive' x y


let compose_exclusive
  (#a: Type u#a)
  (x: option a)
  (y: option a{x `composable_exclusive` y}) =
  match x, y with
  | Some x, None -> Some x
  | None, Some y -> Some y
  | None, None -> None

let exclusive_pcm' (#a: Type u#a) : pcm' (option a) = {
  composable = composable_exclusive;
  op = compose_exclusive;
  one = None
}

let exclusive_pcm (#a: Type u#a) : pcm (option a) = {
  p = exclusive_pcm';
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}


let composable_immutable' (#a: Type u#a) (x y: option a) : prop =
  match x,y with
  | Some x, Some y -> x == y
  | _ -> True

let composable_immutable (#a: Type u#a) : symrel (option a) =
  fun (x y: (option a)) -> composable_immutable' x y


let compose_immutable
  (#a: Type u#a)
  (x: option a)
  (y: option a{x `composable_immutable` y}) =
  match x, y with
  | Some x, _ -> Some x
  | None, Some y -> Some y
  | None, None -> None

let immutable_pcm' (#a: Type u#a) : pcm' (option a) = {
  composable = composable_immutable;
  op = compose_immutable;
  one = None
}

let immutable_pcm (#a: Type u#a) : pcm (option a) = {
  p = immutable_pcm';
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}

module Univ = FStar.Universe

let unit_pcm' : pcm' u#a (Univ.raise_t u#0 u#a unit) = {
    composable = (fun _ _ -> True);
    op = (fun _ _ -> Univ.raise_val u#0 u#a () );
    one =  Univ.raise_val u#0 u#a ()
  }

let higher_unit (x: Univ.raise_t u#0 u#a unit) : Lemma (x == Univ.raise_val u#0 u#a ()) =
  let aux (_ : squash (x =!= Univ.raise_val u#0 u#a ())) : Lemma (False) =
      let x0 = Univ.downgrade_val u#0 u#a x in
      assert(x0 == ())
  in
  Classical.excluded_middle (x == Univ.raise_val u#0 u#a ());
  Classical.or_elim
    #(x == Univ.raise_val u#0 u#a ())
    #(x =!= Univ.raise_val u#0 u#a ())
    #(fun _ -> x == Univ.raise_val u#0 u#a ())
    (fun _ -> ())
    (fun _ -> aux ())

let unit_pcm : pcm u#a (Univ.raise_t u#0 u#a unit)  = {
  p = unit_pcm' u#a;
  comm = (fun _ _  -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun x -> higher_unit x)
}

(*
   Copyright 2024 Microsoft Research

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
module FStar.Dyn

// Note: this file is only a reference implementation showing that the API can
// be implemented safely, we have a separate handcrafted ML implementation using
// `magic`.
// Extracting this file directly results in extra indirections, since `mkdyn`
// would allocate a closure and `undyn` would allocate a closure and a heap
// cell.

noeq type value_type_bundle = { t: Type0; x: t }

let raw_dyn (t: Type u#a) : Type0 = unit -> Dv (b:value_type_bundle {b.t == (unit -> Dv t)})
let to_raw_dyn (#t: Type u#a) (x: t) : raw_dyn t = fun _ -> { t = unit -> Dv t; x = fun _ -> x }

let dyn : Type0 = unit -> Dv value_type_bundle
let mkdyn' (#t: Type u#a) (x: t) : dyn = to_raw_dyn x
let dyn_has_ty (y: dyn) (t: Type u#a) = exists (x: t). y == mkdyn' x
let mkdyn #t x = mkdyn' #t x

let elim_subtype_of s (t: Type { subtype_of s t }) (x: s): t = x

let undyn (#t: Type u#a) (y: dyn { dyn_has_ty y t }) : Dv t =
  let y : raw_dyn t = elim_subtype_of _ _ y in
  let b = y () in
  let c : unit -> Dv t = b.x in
  c ()

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
module Bug1486

open FStar.Tactics.Typeclasses

class functor f = {
  fmap  : (#a:Type) -> (#b:Type) -> (a -> b) -> f a -> f b ;
}

(* Two concrete instances *)
instance functor_list : functor list = { fmap = List.Tot.map }
instance functor_id : functor id = { fmap = fun #_ #_ f a -> f a }

let _ = fmap (fun x -> x + 1) [1 ; 2 ; 3]

let fmap' (#f:Type -> Type) [| functor f |] (#a:Type) (#b:Type) (g:a -> b) (x: f a) : f b = fmap g x

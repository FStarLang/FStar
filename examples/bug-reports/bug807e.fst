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
module Bug807e

let endo : Type u#(a+1) = Type u#a -> Type u#a
let monad_return (t : endo) = #a:Type -> a -> t a
let monad_bind (t:endo) = #a:Type -> #b:Type -> t a -> (a -> t b) -> t b

noeq
type monad_struct =
  | MkMonad :
    car:endo ->
    ret:monad_return car ->
    bnd:monad_bind car ->
    monad_struct

noeq type monad_laws (s : monad_struct) =
  {
    runit : a:Type -> m:s.car a ->
      Lemma (s.bnd #a m (s.ret (* without #_ it fails*)) == m) ;
  }

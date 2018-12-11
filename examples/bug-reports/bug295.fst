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
module Bug295
assume new type t : Type -> Type

assume val lookupRef: #a:Type -> t (t a) -> GTot (t a)
assume val length : #a:Type -> t a -> Tot nat
assume val index: #a:Type -> s:t a -> i:nat{i < length s} -> Tot a

assume val readIndex :  #a:Type  -> r:t (t a)
  -> i:nat
  -> Pure a
        (requires (True))
        (ensures (fun v->
                  (i < length (lookupRef r)
                   /\ v = index (lookupRef r) i)))

assume type erased : Type -> Type
assume val hide : 'a -> GTot (erased 'a)

type s =
  | MkS : x:erased nat -> l:t nat{hide (length l) = x} -> s

val test: x:t nat{length x = 2} -> GTot s
let test x = MkS (hide 2) x

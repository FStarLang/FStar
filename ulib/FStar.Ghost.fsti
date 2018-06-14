(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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

(*
   This module provides an erased type
   to abstract computationally irrelevant values.

   It relies on the GHOST effect defined in Prims.

   [erased a] is an abstract type that receives 
   special treatment in the compiler. 

   1. The type is considered non-informative. 
      So, [Ghost (erased a)] can be subsumed to [Pure (erased a)]

   2. The compiler extracts [erased a] to [unit]

   The type is [erased a] is in a bijection with [a], 
   as witnessed by the [hide] and [reveal] function.

   Importantly, computationally relevant code cannot use [reveal] 
     (it's marked GTot)

   Just like Coq's prop, it is okay to use erased types 
   freely as long as we produce an erased type.
   
*)
module FStar.Ghost
val erased : Type u#a -> Type u#a
val reveal : #a:Type u#a -> erased a -> GTot a
val hide   : #a:Type u#a -> a -> Tot (erased a)

val hide_reveal : #a:Type
                -> x:erased a
                -> Lemma (ensures (hide (reveal x) == x))
                        [SMTPat (reveal x)]

val reveal_hide : #a:Type
                -> x:a
                -> Lemma (ensures (reveal (hide x) == x))
                        [SMTPat (hide x)]

val elift1   : #a:Type
             -> #b:Type
             -> f:(a -> GTot b)
             -> x:erased a
             -> Tot (y:erased b{reveal y == f (reveal x)})

val elift2   : #a:Type
             -> #b:Type
             -> #c:Type
             -> f:(a -> c -> GTot b)
             -> ga:erased a
             -> gc:erased c
             -> Tot (e:erased b{reveal e == f (reveal ga) (reveal gc)})

val elift3   : #a:Type
             -> #b:Type
             -> #c:Type
             -> #d:Type
             -> f:(a -> c -> d -> GTot b)
             -> ga:erased a
             -> gc:erased c
             -> gd:erased d
             -> Tot (e:erased b{reveal e == f (reveal ga) (reveal gc) (reveal gd)})

val elift1_p : #a:Type
             -> #b:Type
             -> #p:(a -> Type)
             -> $f:(x:a{p x} -> GTot b)
             -> r:erased a{p (reveal r)}
             -> Tot (z:erased b{reveal z == f (reveal r)})

val elift2_p : #a:Type
             -> #c:Type
             -> #p: (a -> c -> Type)
             -> #b:Type
             -> $f:(xa:a -> xc:c{p xa xc} -> GTot b)
             -> ra:erased a
             -> rc:erased c{p (reveal ra) (reveal rc)}
             -> Tot (x:erased b{reveal x == f (reveal ra) (reveal rc)})

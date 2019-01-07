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

////////////////////////////////////////////////////////////////////////////////
// The following are all defined notions and need not be trusted
////////////////////////////////////////////////////////////////////////////////
let return (#a:Type) (x:a) : erased a = hide x

let bind (#a:Type) (#b:Type) (x:erased a) (f: (a -> Tot (erased b)))
  : Tot (erased b)
  = let y = reveal x in
    f y

let elift1 (#a #b:Type)
           (f:(a -> GTot b))
           (x:erased a)
  : Tot (y:erased b{reveal y == f (reveal x)})
  = xx <-- x ;
    return (f xx)

let elift2 (#a #b #c:Type)
           (f:(a -> b -> GTot c))
           (x:erased a)
           (y:erased b)
  : Tot (z:erased c{reveal z == f (reveal x) (reveal y)})
  = xx <-- x ;
    yy <-- y;
    return (f xx yy)

let elift3 (#a #b #c #d:Type)
           (f:(a -> b -> c -> GTot d))
           (ga:erased a)
           (gb:erased b)
           (gc:erased c)
  : Tot (gd:erased d{reveal gd == f (reveal ga) (reveal gb) (reveal gc)})
  = a <-- ga;
    b <-- gb;
    c <-- gc;
    return (f a b c)

let elift1_p (#a #b:Type)
             (#p:(a -> Type))
             ($f:(x:a{p x} -> GTot b))
             (r:erased a{p (reveal r)})
  : Tot (z:erased b{reveal z == f (reveal r)})
  = let x : (x:a { p x }) = reveal r in
    return (f x)

let elift2_p (#a #b #c:Type)
             (#p: (a -> b -> Type))
             ($f:(xa:a -> xb:b{p xa xb} -> GTot c))
             (ra:erased a)
             (rb:erased b{p (reveal ra) (reveal rb)})
  : Tot (rc:erased c{reveal rc == f (reveal ra) (reveal rb)})
  = let x = reveal ra in
    let y : (y:b { p x y }) = reveal rb in
    return (f x y)

let elift1_pq (#a #b:Type)
              (#p:(a -> Type))
              (#q:(x:a{p x} -> b -> Type))
              ($f:(x:a{p x} -> GTot (y:b{q x y})))
              (r:erased a{p (reveal r)})
             : Tot (z:erased b{reveal z == f (reveal r)})
  = let x : (x:a { p x }) = reveal r in
    return (f x)

let elift2_pq (#a #b #c:Type)
              (#p:(a -> b -> Type))
              (#q:(x:a -> y:b{p x y} -> c -> Type))
              ($f:(x:a -> y:b{p x y} -> GTot (z:c{q x y z})))
              (ra:erased a)
              (rb:erased b{p (reveal ra) (reveal rb)})
             : Tot (z:erased c{reveal z == f (reveal ra) (reveal rb)})
  = let x = reveal ra in
    let y : (y:b{p x y}) = reveal rb in
    return (f x y)

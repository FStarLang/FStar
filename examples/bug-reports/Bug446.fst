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
module Bug446

open FStar.ST

type wP (a:Type) = st_wp_h int a

effect P (a:Type) (wp:pure_wp a) = PURE a wp

type m (a:Type) (wp:wP a) =
  i0:int -> P (a * int) (fun 'q -> wp (fun a i -> 'q (a, i)) i0)

val works : #a:Type -> #wp1:wP a -> f:m a wp1 -> Tot bool
let works (#a:Type) (#wp1:wP a) (f:m a wp1) : bool = true

assume val fails : #a:Type -> #b:Type -> #wp1:wP a -> #wp2:wP b ->
                   f:m a wp1 -> g:m a (* <- should be b *) wp2 -> Tot bool

(* Horrible error message: Unknown assertion failed -- now good *)

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

module FStar.FunctionalExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type arrow (a:Type) (b:a -> Type) = x:a -> Tot (b x)

[@(deprecated "use arrow instead")]
type efun (a:Type) (b:a -> Type) = arrow a b

type feq (#a:Type) (#b:a -> Type) (f:arrow a b) (g:arrow a b) =
  (forall x.{:pattern (f x) \/ (g x)} f x == g x)

inline_for_extraction
val on_domain (a:Type) (#b:a -> Type) (f:arrow a b)
  : Tot (arrow a b)

let is_restricted (a:Type) (#b:a -> Type) (f:arrow a b) =
    on_domain a f == f

let restricted_t (a:Type) (b:a -> Type) =
  f:arrow a b{is_restricted a f}

val feq_on_domain (#a:Type) (#b:a -> Type) (f:arrow a b)
  : Lemma (feq (on_domain a f) f)
          [SMTPat (on_domain a f)]

val extensionality (a:Type) (b:a -> Type) (f:arrow a b) (g:arrow a b)
  : Lemma (ensures (feq #a #b f g <==> (on_domain a f == on_domain a g)))
          [SMTPat (feq #a #b f g)]

val idempotence_on_domain (#a:Type) (#b:a -> Type) (f:arrow a b)
  : Lemma (on_domain a (on_domain a f) == on_domain a f)
          [SMTPat (on_domain a (on_domain a f))]

let on_dom (a:Type) (#b:a -> Type) (f:arrow a b)
  : restricted_t a b
  = on_domain a f

let restricted_t_2 (a:Type) (b:Type) (c:Type) =
   f:restricted_t a (fun _ ->
     restricted_t b (fun _ ->
     c))

let restricted_t_2_idem (#a #b #c:Type) (f: restricted_t_2 a b c)
  : Lemma (on_domain a f == f)
  = ()

let on_dom2 (#a #b:Type) (#c:Type) (f:(a -> b -> Tot c)) : restricted_t_2 a b c =
    on_dom a (fun x ->
    on_dom b (fun y ->
    f x y))

let on_dom2_interp (#a #b #c:Type) (f: (a -> b -> Tot c)) (x:a) (y:b)
    : Lemma (on_dom2 f x y == f x y)
            [SMTPat (on_dom2 f x y)]
    = ()


(****** GTot version ******)

type arrow_g (a:Type) (b:a -> Type) = x:a -> GTot (b x)

[@(deprecated "use arrow_g instead")]
type efun_g (a:Type) (b:a -> Type) = arrow_g a b

type feq_g (#a:Type) (#b:a -> Type) (f:arrow_g a b) (g:arrow_g a b) =
  (forall x.{:pattern (f x) \/ (g x)} f x == g x)

inline_for_extraction
val on_domain_g (a:Type) (#b:a -> Type) (f:arrow_g a b)
  : Tot (arrow_g a b)

let is_restricted_g (a:Type) (#b:a -> Type) (f:arrow_g a b) =
    on_domain_g a f == f

let restricted_g_t (a:Type) (b:a -> Type) =
  f:arrow_g a b{is_restricted_g a f}

val feq_on_domain_g (#a:Type) (#b:a -> Type) (f:arrow_g a b)
  : Lemma (feq_g (on_domain_g a f) f)
          [SMTPat (on_domain_g a f)]

val extensionality_g (a:Type) (b:a -> Type) (f g:arrow_g a b)
  : Lemma (ensures (feq_g #a #b f g <==> (on_domain_g a f == on_domain_g a g)))
          [SMTPat (feq_g #a #b f g)]

val idempotence_on_domain_g (#a:Type) (#b:a -> Type) (f:arrow_g a b)
  : Lemma (on_domain_g a (on_domain_g a f) == on_domain_g a f)
          [SMTPat (on_domain_g a (on_domain_g a f))]

let on_dom_g (a:Type) (#b:a -> Type) (f:arrow_g a b)
  : restricted_g_t a b
  = on_domain_g a f

let restricted_g_t_2 (a:Type) (b:Type) (c:Type) =
   f:restricted_g_t a (fun _ ->
     restricted_g_t b (fun _ ->
     c))

let restricted_g_t_2_idem (#a #b #c:Type) (f: restricted_g_t_2 a b c)
  : Lemma (on_domain_g a f == f)
  = ()

let on_dom_g2 (#a #b:Type) (#c:Type) (f:(a -> b -> GTot c)) : restricted_g_t_2 a b c =
    on_dom_g a (fun x ->
    on_dom_g b (fun y ->
    f x y))

let on_dom_g2_interp (#a #b #c:Type) (f: (a -> b -> GTot c)) (x:a) (y:b)
    : Lemma (on_dom_g2 f x y == f x y)
            [SMTPat (on_dom_g2 f x y)]
    = ()

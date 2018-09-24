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

type efun (a:Type) (b:a -> Type) = x:a -> Tot (b x)

type feq (#a:Type) (#b:a -> Type) (f:efun a b) (g:efun a b) =
  (forall x.{:pattern (f x) \/ (g x)} f x == g x)

abstract let on_domain (a:Type) (#b:a -> Type) (f:efun a b) :efun a b = fun (x:a) -> f x

let lemma_on_domain_interpretation (#a:Type) (#b:a -> Type) (f:efun a b)
  :Lemma (feq (on_domain a f) f)
	 [SMTPat (on_domain a f)]
  = ()

assume Extensionality : forall (a:Type) (b:a -> Type) (f:efun a b) (g:efun a b).
                        {:pattern feq #a #b f g} feq #a #b f g <==> (on_domain a f == on_domain a g)

let lemma_on_domain_is_idempotent (#a:Type) (#b:a -> Type) (f:efun a b)
  :Lemma (on_domain a (on_domain a f) == on_domain a f)
         [SMTPat (on_domain a (on_domain a f))]
  = ()

(****** GTot version ******)

type efun_g (a:Type) (b:a -> Type) = x:a -> GTot (b x)

type feq_g (#a:Type) (#b:a -> Type) (f:efun_g a b) (g:efun_g a b) =
  (forall x.{:pattern (f x) \/ (g x)} f x == g x)

abstract let on_domain_g (a:Type) (#b:a -> Type) (f:efun_g a b) :efun_g a b = fun (x:a) -> f x

let lemma_on_domain_interpretation_g (#a:Type) (#b:a -> Type) (f:efun_g a b)
  :Lemma (feq_g (on_domain_g a f) f)
	 [SMTPat (on_domain_g a f)]
  = ()

assume GhostExtensionality : forall (a:Type) (b:a -> Type) (f:efun a b) (g:efun a b).
                             {:pattern feq_g #a #b f g} feq_g #a #b f g <==> (on_domain_g a f == on_domain_g a g)

let lemma_on_domain_is_idempotent_g (#a:Type) (#b:a -> Type) (f:efun_g a b)
  :Lemma (on_domain_g a (on_domain_g a f) == on_domain_g a f)
         [SMTPat (on_domain_g a (on_domain_g a f))]
  = ()

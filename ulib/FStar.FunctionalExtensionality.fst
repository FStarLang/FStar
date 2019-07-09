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

module FStar.FunctionalExtensionality
#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0"

inline_for_extraction
let on_domain (a:Type) (#b:a -> Type) (f:arrow a b)
  = f

let feq_on_domain (#a:Type) (#b:a -> Type) (f:arrow a b)
  = ()

let idempotence_on_domain #a #b f
  = ()

let extensionality a b f g
  = admit() //the main axiom of this module


(****** GTot version ******)

let on_domain_g (a:Type) (#b:a -> Type) (f:arrow_g a b)
  = f

let feq_on_domain_g (#a:Type) (#b:a -> Type) (f:arrow_g a b)
  = ()

let idempotence_on_domain_g #a #b f
  = ()

let extensionality_g a b f g
  = admit () //variant of the main axiom

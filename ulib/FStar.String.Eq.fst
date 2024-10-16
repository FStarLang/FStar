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

module FStar.String.Eq

open FStar.List.Tot.Properties
module EqRaw = FStar.Class.Eq.Raw
module Eq  = FStar.Class.Eq

open FStar.String
open FStar.String.Base
open FStar.String.Properties

let decides_eqtype (#a:eqtype) (f : a -> a -> bool) : prop =
  forall x y. f x y <==> x = y

let streq'_decides_deq () :
 Lemma (decides_eqtype streq')
= introduce forall x y. streq' x y <==> x == y
  with streq'_iff_eq x y

instance streq'_is_deq : EqRaw.deq string = {
  eq = streq'
}

///  Propeq properties 

let streq'_decides_eq () :
 Lemma (Eq.decides_eq streq')
= introduce forall x y. streq' x y <==> x == y
  with streq'_iff_propeq x y

instance streq'_is_eq : Eq.deq string = {
  raw    = streq'_is_deq;
  eq_dec = streq'_decides_deq ()
}

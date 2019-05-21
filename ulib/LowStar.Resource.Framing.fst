(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Resource.Framing

open FStar.Algebra.CommMonoid.Equiv
open FStar.Tactics.CanonCommMonoidSimple.Equiv

open LowStar.Resource

let resource_equiv : equiv resource = 
  EQ equal 
     equal_refl 
     equal_symm 
     equal_trans

let resource_monoid : cm resource resource_equiv =
  CM empty_resource 
     (<*>) 
     equal_comm_monoid_left_unit 
     equal_comm_monoid_associativity 
     equal_comm_monoid_commutativity 
     equal_comm_monoid_cong

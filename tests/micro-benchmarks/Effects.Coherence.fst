(*
   Copyright 2008-2020 Microsoft Research

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

module Effects.Coherence

(*
 * Unit tests for the coherence of effects orderings
 *)

type repr (a:Type) (_:unit) = a

let return (a:Type) (x:a) : repr a () = x
let bind (a:Type) (b:Type) (f:repr a ()) (g:a -> repr b ()) : repr b () = g f

layered_effect {
  M1 : Type -> eqtype_as_type unit -> Effect
  with
  repr = repr;
  return = return;
  bind = bind
}

new_effect M2 = M1
new_effect M3 = M1
new_effect M4 = M1
new_effect M5 = M1

let lift_m_m (a:Type) (f:repr a ()) : repr a () = f

sub_effect M1 ~> M3 = lift_m_m
sub_effect M2 ~> M3 = lift_m_m
sub_effect M1 ~> M4 = lift_m_m

//loses unique least upper bound of M1 and M2
[@@expect_failure [329]]  
sub_effect M2 ~> M4 = lift_m_m

//changes the least upper bound of M1 and M2 to M2 from earlier M3
[@@expect_failure [329]]
sub_effect M1 ~> M2 = lift_m_m

//TODO: this is silently ignored, should add a warning
sub_effect M1 ~> M3 = lift_m_m

sub_effect M3 ~> M5 = lift_m_m

//there already exists an edge M1 to M5 (via M3)
[@@expect_failure [329]]
polymonadic_subcomp M1 <: M5 = lift_m_m

//M1 and M5 already have a least upper bound (M5)
[@@expect_failure [329]]
polymonadic_bind (M1, M5) |> M5 = bind

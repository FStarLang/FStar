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
 * Unit tests for effects orderings
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

let lift_pure_m (a:Type) (wp:_) (f:eqtype_as_type unit -> PURE a wp)
  : Pure (repr a ()) (requires wp (fun _ -> True)) (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
    f ()
sub_effect PURE ~> M1 = lift_pure_m


(*
 * Define an identity lift
 *)

let lift_m_m (a:Type) (f:repr a ()) : repr a () = f

(*
 * Define a stricter lift, that (unnecessarily) requires a proof of False
 *)
let lift_m_m' (a:Type) (f:repr a ())
  : Pure (repr a ()) (requires False) (ensures fun _ -> True)
  = f

(*
 * We now build:
 *
 *   M1 --> M3
 *   M2 --> M3
 *)

sub_effect M1 ~> M3 = lift_m_m
sub_effect M2 ~> M3 = lift_m_m

assume val f1 : unit -> M1 unit ()


(*
 * As expected, M1 can be lifted to M3
 *)
let f2 () : M3 unit () = f1 ()


(*
 * Now add an edge from M1 to M2:
 *
 * With this edge, we are adding a new path from M1 to M3, that goes via M2
 *
 * At this point, to lift M1 to M3, F* will use this new path,
 *   so it looks like this now:
 *
 * M1 --> M2 --> M3
 *
 * To better test this, when we define life from M1 to M2,
 *   we use the artificial requires False lift
 *)
sub_effect M1 ~> M2 = lift_m_m'


(*
 * And now, lifting M1 to M3 fails, this same code succeeded earlier
 *
 * The reason is that lifting goes through M2 now and M2 -> M3 requires False
 *)
[@@expect_failure]
let f3 () : M3 unit () = f1 ()

(*
 * Similarly, composing M1 and M3 fails,
 *   since the only way to compose them is via lifting M1, which requires False
 *)
assume val f4 : unit -> M3 unit ()

[@@ expect_failure]
let f5 () : M3 unit () = f1 (); f4 ()

(*
 * But, if we define a polymonadic bind between M1 and M3,
 *   that always takes precedence, so this will succeed
 *)

let m_m_pbind (a b:Type) (f:repr a ()) (g:a -> repr b ()) : repr b () = g f

polymonadic_bind (M1, M3) |> M3 = m_m_pbind

let f6 () : M3 unit () = f1 (); f4 ()


(*
 * However, composing M3 and M1 would still fail,
 *   since that would try to lift M1 first
 *)
[@@expect_failure]
let f7 () : M3 unit () = f4 (); f1 ()


//Testing for cycles and unique upper bounds

new_effect M4 = M1
new_effect M5 = M1
new_effect M6 = M1
new_effect M7 = M1


(*
 * Make M6 as the least upper bound of M4 and M5
 *)

sub_effect M4 ~> M6 = lift_m_m
sub_effect M5 ~> M6 = lift_m_m

(*
 * Try making M7 as another upper bound of M4 and M5
 *
 * It will fail
 *)

sub_effect M4 ~> M7 = lift_m_m
[@@expect_failure]
sub_effect M5 ~> M7 = lift_m_m

sub_effect M6 ~> M7 = lift_m_m

(*
 * This induces a cycle, M5 -> M6 -> M7 -> M5
 *)
[@@expect_failure]
sub_effect M7 ~> M5 = lift_m_m

(*
   Copyright 2019 Microsoft Research

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

module RST


/// A sample implementation of the RST effect used in Steel
///   illustrating the use of resources as indices, we don't consider
///   wps here.
///
/// The main subtlety here is the dependent resource parametric `return`
///   combinator of the effect (`returnc`)
///   which is later turned into an action using reflect (`return`),
/// 
///   and finally used to return dependent resources to the context (`test`).
///
/// The normal formulation (of using `emp` and `fun _ -> emp` indexed `return`)
///   gets into variable binding issues when returning dependent resources.


open FStar.HyperStack.ST

module HS = FStar.HyperStack


assume type resource : Type0


type repr (a:Type) (r_in:resource) (r_out:a -> resource) (b:Type0) =
  unit -> STATE a (fun p h -> forall x h1. p x h1)


let returnc (a:Type) (x:a) (r:a -> resource)
: repr a (r x) r True
= fun _ -> x

let bind (a:Type) (b:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (b_f:Type0)
  (r_out_g:b -> resource) (b_g:Type0)
  (f:repr a r_in_f r_out_f b_f) (g:(x:a -> repr b (r_out_f x) r_out_g b_g))
: Pure (repr b r_in_f r_out_g b_f)
  (requires b_f /\ b_g)
  (ensures fun _ -> True)
= fun _ ->
  let x = f () in
  (g x) ()

(* We now derive these default implementations of subcomp and if_then_else *)

// let subcomp (a:Type)
//   (r_in:resource) (r_out:a -> resource) (b:Type0)
//   (f:repr a r_in r_out b)
// : (repr a r_in r_out b)
// = f

// let if_then_else (a:Type)
//   (r_in:resource) (r_out:a -> resource) (b:Type0)
//   (f:repr a r_in r_out b) (g:repr a r_in r_out b)
//   (p:Type0)
// : Type
// = repr a r_in r_out b

reifiable reflectable
effect {
  RSTATE (a:Type) (_:resource) (_:a -> resource) (_:Type0)
  with {repr = repr;
        return = returnc;
        bind = bind}
}

let return (#a:Type) (#r:a -> resource) (x:a)
: RSTATE a (r x) r True
= RSTATE?.reflect (returnc a x r)

let lift_pure_rst (a:Type) (wp:pure_wp a) (r:resource) (f:unit -> PURE a wp)
: Pure (repr a r (fun _ -> r) True)
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= FStar.Monotonic.Pure.elim_pure_wp_monotonicity_forall ();
  fun _ -> f ()

sub_effect PURE ~> RSTATE = lift_pure_rst


assume val emp : resource

assume val array : Type0
assume val array_resource (a:array) : resource

assume val alloc (_:unit) : RSTATE array emp array_resource True

let test ()
: RSTATE array emp array_resource True
= let ptr = alloc () in
  return ptr

type t =
  | C : t
  | D : t

assume val rst_unit (_:unit) : RSTATE unit emp (fun _ -> emp) True

let test_match (x:t) : RSTATE unit emp (fun _ -> emp) True =
  match x with
  | C -> rst_unit ()
  | D -> rst_unit ()


(*
 * Following example showcases a bug in checking match terms for layered effects
 *
 * When typechecking the pattern `C a x`, we generate a term with projectors and discriminators
 *   for each of the pattern bvs, a and x in this case, and those terms are then lax checked
 * Crucially when lax checking pat_bv_tm for `x`, `a` must be in the environment,
 *   earlier it wasn't
 *)

noeq
type m : Type -> Type =
| C1 : a:Type -> x:a -> m a
| D1 : a:Type -> x:a -> m a

let test_match2 (a:Type) (f:m a) : RSTATE unit emp (fun _ -> emp) True
= match f with
  | C1 a x -> rst_unit ()
  | D1 a x -> rst_unit ()


assume val false_pre (_:squash False) : RSTATE unit emp (fun _ -> emp) True

[@@expect_failure]
let test_false_pre () : RSTATE unit emp (fun _ -> emp) True
= false_pre ()


/// Test that bind precondition is checked

assume val f_test_bind (_:unit) : RSTATE unit emp (fun _ -> emp) True
assume val g_test_bind (_:unit) : RSTATE unit emp (fun _ -> emp) False

[@@expect_failure]
let test_bind () : RSTATE unit emp (fun _ -> emp) True
= f_test_bind ();
  g_test_bind ()

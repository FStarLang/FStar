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


type repr (a:Type) (r_in:resource) (r_out:a -> resource) =
  unit -> STATE a (fun p h -> forall x h1. p x h1)


let returnc (a:Type) (x:a) (r:a -> resource)
: repr a (r x) r
= fun _ -> x

let bind (a:Type) (b:Type)
  (r_in_f:resource) (r_out_f:a -> resource) (r_out_g:b -> resource)
  (f:repr a r_in_f r_out_f) (g:(x:a -> repr b (r_out_f x) r_out_g))
: repr b r_in_f r_out_g
= fun _ ->
  let x = f () in
  (g x) ()

let subcomp (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (f:repr a r_in r_out)
: (repr a r_in r_out)
= f

let if_then_else (a:Type)
  (r_in:resource) (r_out:a -> resource)
  (f:repr a r_in r_out) (g:repr a r_in r_out)
  (p:Type0)
: Type
= repr a r_in r_out


reifiable reflectable
layered_effect {
  RSTATE : a:Type -> resource -> (a -> resource) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let return (#a:Type) (#r:a -> resource) (x:a)
: RSTATE a (r x) r
= RSTATE?.reflect (returnc a x r)


let lift_pure_rst (a:Type) (wp:pure_wp a) (r:resource) (f:unit -> PURE a wp)
: repr a r (fun _ -> r)
= admit (); fun _ -> f ()  //dropping wp

sub_effect PURE ~> RSTATE = lift_pure_rst


assume val emp : resource

assume val array : Type0
assume val array_resource (a:array) : resource

assume val alloc (_:unit) : RSTATE array emp array_resource

let test ()
: RSTATE array emp array_resource
= let ptr = alloc () in
  return ptr


(*
 * Following example showcases a bug in checking match terms for layered effects
 *
 * When typechecking the pattern `C a x`, we generate a term with projectors and discriminators
 *   for each of the pattern bvs, a and x in this case, and those terms are then lax checked
 * Crucially when lax checking pat_bv_tm for `x`, `a` must be in the environement,
 *   earlier it wasn't
 *)

noeq
type m : Type -> Type =
| C : a:Type -> x:a -> m a


assume val rst_unit (_:unit) : RSTATE unit emp (fun _ -> emp)

let test_match (a:Type) (f:m a) : RSTATE unit emp (fun _ -> emp)
= match f with
  | C a x -> rst_unit ()

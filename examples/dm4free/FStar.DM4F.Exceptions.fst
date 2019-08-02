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
module FStar.DM4F.Exceptions

(**********************************************************
 * Dijkstra Monads for Free : Exceptions
 *
 * Example of an exception monad effect, with a lift from
 * the Pure effect into it and an example of how both
 * intrinsic and extrinsic proof methods can be used
 * on a simple division function.
 *
 **********************************************************)

(* The underlying representation type *)
let ex (a:Type) = unit -> M (either a exn)

(* Monad definition *)
val return_ex : (a:Type) -> (x:a) -> ex a
let return_ex a x = fun _ -> Inl x

val bind_ex : (a:Type) -> (b:Type) -> (f:ex a) -> (g:a -> ex b) -> ex b
let bind_ex a b f g = fun _ ->
  let r = f () in
  match r with
  | Inr e -> Inr e
  | Inl x -> g x ()

let raise0 (a:Type) (e:exn) : ex a = fun _ -> Inr e

(* Define the new effect using DM4F *)
total reifiable reflectable new_effect {
  EXN : (a:Type) -> Effect
  with repr     = ex
     ; bind     = bind_ex
     ; return   = return_ex
     ; raise (#a:Type) = raise0 a
}


let raise = EXN?.raise

(* An effect to alias easily write pre- and postconditions *)
(* Note: we use Type0 instead of EXN?.pre to avoid having to thunk everything. *)
effect Exn (a:Type) (pre:Type0) (post:EXN?.post a) =
  EXN a (fun (_:unit) (p:EXN?.post a) -> pre /\
          (forall (r:either a exn). (pre /\ post r) ==> p r))

(* Another alias. Ex a is the effect type for total exception-throwing
 * programs. i.e. Any program of type `Ex a´ will throw or finish
 * correctly, but never loop. *)
effect Ex (a:Type) = EXN a (fun _ p -> forall x. p x)

(*
 * We now show `div´ to be correct in two ways. The property we show is
 * that if `div´ throws, then the divisor was zero; and if it doesn't,
 * then the divisor was not zero and the result (z) is the division of i
 * and j.
 *
 * In the first definition, we give a strong type to `div´: we make use
 * of `Exn´ to give pre- and postconditions to the function, specifying
 * the property we want. This is known as an intrinsic proof: it's
 * within the definition.
 *
 * In the second, we give a very lax type to div, namely `Ex int´ (note
 * it is different from Exn). This type is only implying that calling
 * div will either throw an exception or return an int, but there's no
 * specification about the result or about when exceptions occur.
 *
 * As `Ex´ is a  effect, we can reason about `div´ outside of
 * its definition by turning it into a pure function. This is what is
 * done in the `lemma_div_extrinsic´ lemma.
 *
 * For primitive effects, this is impossible since logical properties
 * (in proof-irrelevant contexts) only make sense for pure and total
 * terms, so one is only able to do proofs intrinsically.
 *)

exception Division_by_zero

val div_intrinsic : i:nat -> j:int -> Exn int
  (requires True)
  (ensures (function | Inr Division_by_zero -> j=0 | Inl z -> j<>0 /\ z = i / j
                     | _ -> True))
let div_intrinsic i j =
  if j=0 then raise Division_by_zero
  else i / j

 let div_extrinsic (i:nat) (j:int) : Ex int =
  if j=0 then raise Division_by_zero
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) () with
         | Inr Division_by_zero -> j = 0
         | Inl z -> j <> 0 /\ z = i / j) = ()

(*
 * We can also build a new action "on the fly" using reflect!
 * Here we define raise_ as a pure function working with the
 * representation of Ex.
 *)
val raise_ : a:Type -> e:exn -> Tot (EXN?.repr a (fun (_:unit) (p:EXN?.post a) -> p (Inr e)))
let raise_ a (e:exn) (_:unit) = Inr e

(* We reflect it back to Exn *)
 let raise__ (a:Type) (e:exn) : Exn a True (fun r -> r == Inr e)
  = EXN?.reflect (raise_ a e)

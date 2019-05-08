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
module FStar.DM4F.ExnSt

(**********************************************************
 * Dijkstra Monads for Free : Exceptions with state
 *
 * Exceptions over (integer) state (state dropped when raising)
 *
 **********************************************************)

module IntST = FStar.DM4F.IntST

(* The underlying representation type *)
let exnst a = int -> M (option (a * int))

(* Monad definition *)
val return : (a:Type) -> (x:a) -> exnst a
let return a x = fun s -> Some (x, s)

val bind : (a:Type) -> (b:Type) ->
           (f:exnst a) -> (g:a -> exnst b) -> exnst b
let bind a b f g =
  fun s0 ->
    let res = f s0 in
    match res with
    | None -> None
    | Some (ret, s1) -> g ret s1

let raise (a:Type) : exnst a = fun _ -> None

(* Define the new effect using DM4F *)
total reifiable reflectable new_effect {
  EXNST: a:Type -> Effect with
    repr    = exnst;
    bind    = bind;
    return  = return;
    raise   = raise
}

let stint (a:Type)= FStar.DM4F.ST.st int a

(* A lift from a previously defined state effect *)
sub_effect IntST.STINT ~> EXNST {
  lift = fun (a:Type) (e:stint a) -> (fun s -> let z = e s in Some z) <: exnst a
}

(* Pre-/postcondition variant *)
effect ExnSt (a:Type) (req:EXNST?.pre) (ens:int -> option (a * int) -> GTot Type0) =
       EXNST a
         (fun (h0:int) (p:EXNST?.post a) -> req h0 /\ (forall r. (req h0 /\ ens h0 r) ==> p r))

(* Total variant *)
effect S (a:Type) =
       EXNST a (fun h0 p -> forall x. p x)

(*
 * Proving intrinsically and extrinsically again, now also handling
 * state in between. The specification now also guarantees that div
 * doesn't modify the state.
 *)

let div_intrisic_spec (i :nat) (j:int) (h0:int) (x:option (int * int)) : Type0 =
  match x with
  | None -> j=0
  | Some (z, h1) -> h0 = h1 /\ j<>0 /\ z = i / j

val div_intrinsic : i:nat -> j:int -> ExnSt int
  (requires (fun h -> True))
  (ensures (fun h0 x -> div_intrisic_spec i j h0 x))

let div_intrinsic i j =
    if j = 0 then (
        (* Despite the incr (implicitly lifted), the state is reset *)
        IntST.incr ();
        EXNST?.raise int
    ) else
        i / j

 let div_extrinsic (i:nat) (j:int) : S int =
    if j = 0 then
      begin
        IntST.incr () ;
        EXNST?.raise int
      end
    else
      i / j

let lemma_div_extrinsic (i:nat) (j:int) (h0:int) :
  Lemma (match reify (div_extrinsic i j) h0 with
         | None -> j = 0
         | Some (z, h1) -> h0 = h1 /\ j <> 0 /\ z = i / j) = ()

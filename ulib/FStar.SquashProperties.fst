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
module FStar.SquashProperties

open FStar.Constructive

open FStar.Squash

val join_squash : #a:Type -> squash (squash a) -> GTot (squash a)
let join_squash #a s = bind_squash #(squash a) #a s (fun x -> x)

val squash_arrow : #a:Type -> #p:(a -> Type) ->
  $f:(x:a -> GTot (squash (p x))) -> GTot (squash (x:a -> GTot (p x)))
let squash_arrow #a #p f = squash_double_arrow (return_squash f)

val forall_intro : #a:Type -> #p:(a -> Type) ->
  $f:(x:a -> Lemma (p x)) -> Lemma (x:a -> GTot (p x))(* (forall (x:a). p x) *)
let forall_intro #a #p f =
  let ff : (x:a -> GTot (squash (p x))) = (fun x -> f x; get_proof (p x)) in
  give_proof #(x:a -> GTot (p x)) (squash_arrow #a #p ff)


// currently unused
// val squash_elim : a:Type -> #b:Type -> t1:b -> t2:b ->
//       (       a -> Tot (ceq t1 t2)) ->
//   Tot (squash a -> Tot (ceq t1 t2))

(* assume val tt (t:Type) : squash t *)

(* assume val squash_mem_elim : a:Type -> #b:Type -> t1:b -> t2:b -> *)
(*       (x:squash a -> t:(squash a -> Type) -> Tot (t ())) -> *)
(*   Tot (x:squash a -> t:(squash a -> Type) -> Tot (t x)) *)

(* get_proof and give_proof are phrased in terms of squash *)

(* The whole point of defining squash is to soundly allow define excluded_middle;
   here this follows from get_proof and give_proof *)

val bool_of_or : #p:Type -> #q:Type -> Prims.sum p q ->
  Tot (b:bool{(b ==> p) /\ (not(b) ==> q)})
let bool_of_or #p #q t =
  match t with
  | Prims.Left  _ -> true
  | Prims.Right _ -> false

val excluded_middle : p:Type -> GTot (squash (b:bool{b <==> p}))
let excluded_middle (p:Type) = map_squash (join_squash (get_proof (p \/ (~p)))) bool_of_or


val excluded_middle_squash : p:Type0 -> GTot (p \/ ~p)
let excluded_middle_squash p =
  bind_squash (excluded_middle p) (fun x ->
  if x then
    map_squash (get_proof p) (Prims.Left #p)
  else
    return_squash (Prims.Right #_ #(~p) (return_squash (fun (h:p) ->
                                   give_proof (return_squash h);
                                   false_elim #False ()))))

(* we thought we might prove proof irrelevance by Berardi ... but didn't manage *)

(* Conditional on any Type -- unused below *)
val ifProp: #p:Type0 -> b:Type0 -> e1:squash p -> e2:squash p -> GTot (squash p)
let ifProp #p b e1 e2 =
   bind_squash (excluded_middle_squash b) 
	       (fun (x:Prims.sum b (~ b)) -> 
		match x with
	        | Prims.Left _ -> e1
		| Prims.Right _ -> e2)

(* The powerset operator *)
type pow (p:Type) = p -> GTot bool

noeq type retract 'a 'b : Type =
  | MkR: i:('a -> GTot 'b) ->
         j:('b -> GTot 'a) ->
         inv:(x:'a -> GTot (ceq (j (i x)) x)) ->
         retract 'a 'b

noeq type retract_cond 'a 'b : Type =
  | MkC: i2:('a -> GTot 'b) ->
         j2:('b -> GTot 'a) ->
         inv2:(retract 'a 'b -> x:'a -> GTot (ceq (j2 (i2 x)) x)) ->
         retract_cond 'a 'b

(* unused below *)
val ac: r:retract_cond 'a 'b -> retract 'a 'b -> x:'a ->
          GTot (ceq ((MkC?.j2 r) (MkC?.i2 r x)) x)
let ac (MkC _ _ inv2) = inv2

let false_elim (#a:Type) (f:False) : Tot a
  = match f with

val l1: (a:Type0) -> (b:Type0) -> GTot (squash (retract_cond (pow a) (pow b)))
let l1 (a:Type) (b:Type) =
   bind_squash (excluded_middle_squash (retract (pow a) (pow b))) 
	      (fun (x:Prims.sum (retract (pow a) (pow b)) (~ (retract (pow a) (pow b)))) ->
	         match x with
		 | Prims.Left (MkR f0 g0 e) -> 
		   return_squash (MkC f0 g0 (fun _ -> e))
		 | Prims.Right nr ->
		   let f0 (x:pow a) (y:b) = false in
		   let g0 (x:pow b) (y:a) = false in
		   map_squash nr (fun (f:(retract (pow a) (pow b) -> GTot False)) -> 
				  MkC f0 g0 (fun r x -> false_elim (f r))))

(* The paradoxical set *)
type u = p:Type -> Tot (squash (pow p))

(* NS: FAILS TO CHECK BEYOND HERE ... TODO, revisit *)

(* Bijection between U and (pow U) *)
assume val f : u -> Tot (squash (pow u))
#set-options "--print_universes"
(* let f x = x u  *) //fails here without a means of denoting universes

// val g : squash (pow U) -> Tot U
// let g sh = fun (x:Type) -> 
//   let (slX:squash (pow U -> Tot (pow x))) = map_squash (l1 x U) MkC?.j2 in 
//   let (srU:squash (pow U -> Tot (pow U))) = map_squash (l1 U U) MkC?.i2 in 
//   bind_squash srU (fun rU ->
//   bind_squash slX (fun lX ->
//   bind_squash sh (fun h ->
//   return_squash (lX (rU h)))))

// (* This only works if importing FStar.All.fst, which is nonsense *)
// val r : U
// let r =
//   let ff : (U -> Tot (squash bool)) =
//       (fun (u:U) -> map_squash (u U) (fun uu -> not (uu u))) in
//   g (squash_arrow ff)

(* CH: stopped here *)
(* val not_has_fixpoint : squash (ceq (r U r) (not (r U r))) *)
(* let not_has_fixpoint = Refl #bool #(r U r) *)


(* otherwise we could assume proof irrelevance as an axiom;
   note that proof relevance shouldn't be derivable for squash types *)
(* val not_provable : unit -> *)
(*   Tot (cnot (ceq (return_squash true) (return_squash false))) *)
(* val not_provable : unit -> *)
(*   Tot (squash (cnot (ceq (return_squash true) (return_squash false)))) *)

// type cheq (#a:Type) (x:a) : #b:Type -> b -> Type =
//   | HRefl : cheq #a x #a x

(* val not_provable : unit -> *)
(*   Tot (cimp (cheq (return_squash #(b:bool{b=true})  true) *)
(*                   (return_squash #(b:bool{b=false}) false)) (squash cfalse)) *)
(* let not_provable () = *)
(*   (fun h -> match h with *)
(*             | HRefl ->  *)
(*               assert(return_squash #(b:bool{b=true}) true == *)
(*                      return_squash #(b:bool{b=false}) false); *)
(*               bind_squash (return_squash #(b:bool{b=true})  true) (fun btrue -> *)
(*               bind_squash (return_squash #(b:bool{b=false}) false) (fun bfalse -> *)
(*               assert (btrue <> bfalse); magic()))) *)

(* TODO:
  - play with this a bit more; try out some examples
    + search for give_proof / get_proof
*)

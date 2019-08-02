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
module StExn.Handle
let pre = int -> Type0
let post (a:Type) = (option a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0
unfold let return_wp (a:Type) (x:a) (n0:int) (post:post a) =
  forall y. y==(Some x, n0) ==> post y

//working around #517 by adding an explicit 'val'
unfold val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (function
	| (None, n1) -> post (None, n1)
	| (Some x, n1) -> g x n1 post)

unfold let if_then_else  (a:Type) (p:Type)
                            (wp_then:wp a) (wp_else:wp a)
                            (h0:int) (post:post a) =
     l_ITE p
        (wp_then h0 post)
	(wp_else h0 post)
unfold let ite_wp        (a:Type)
                            (wp:wp a)
                            (h0:int) (post:post a) =
  wp h0 post
unfold let stronger  (a:Type) (wp1:wp a) (wp2:wp a) =
     (forall (p:post a) (h:int). wp1 h p ==> wp2 h p)

unfold let close_wp      (a:Type) (b:Type)
                            (wp:(b -> GTot (wp a)))
                            (h:int) (p:post a) =
     (forall (b:b). wp b h p)
unfold let assert_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p /\ wp h q
unfold let assume_p      (a:Type) (p:Type)
                            (wp:wp a)
                            (h:int) (q:post a) =
     p ==> wp h q
unfold let null_wp       (a:Type)
                            (h:int) (p:post a) =
     (forall (x:option a) (h:int). p (x,h))
unfold let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (option a * int) (wp n0)

unfold val bind: (a:Type) -> (b:Type) -> (wp0:wp a)
		 -> (f:repr a wp0)
		 -> (wp1:(a -> Tot (wp b)))
		 -> (g:(x:a -> Tot (repr b (wp1 x))))
		 -> Tot (repr b (bind_wp range_0 a b wp0 wp1))
let bind a b wp0 f wp1 g
  = fun n0 -> admit(); match f n0 with
		    | None, n1 -> None, n1
		    | Some x, n1 -> g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> (Some x, n0)

let get (u:unit) : repr int (fun n0 post -> post (Some n0, n0))
  = fun n0 -> Some n0, n0

//this counts the number of exceptions that are raised
val raise : a:Type0 -> Tot (repr a (fun h0 (p:post a) -> p (None, h0 + 1)))
let raise a (h:int) = None, h + 1

let get_cps_type = (u: unit) -> Tot (repr int (fun n0 post -> post (Some n0, n0)))
let raise_cps_type = a:Type0 -> Tot (repr a (fun h0 (p:post a) -> p (None, h0 + 1)))


//adding a reflect do define a handler below,
//but want to restrict it so that it is private to this module
//although we don't have syntax for that yet ...
reifiable reflectable new_effect {
  StateExn : a:Type -> wp:wp a -> Effect
  with //repr is new; it's the reprentation of ST as a value type
      repr         = repr
      //bind_wp is exactly as it is currently
      //produced by the *-translation of bind above
    ; bind_wp      = bind_wp
      //bind is new, it is the elaboration of the bind above
    ; bind         = bind
    //return_wp is a renaming of the current return, it is the *-translation of the return above
    ; return_wp    = return_wp
    //return is new; it is the elaboration of the return above
    ; return       = return
    //the remaining are just as what we have now
    ; if_then_else = if_then_else
    ; ite_wp       = ite_wp
    ; stronger     = stronger
    ; close_wp     = close_wp
    ; assert_p     = assert_p
    ; assume_p     = assume_p
    ; null_wp      = null_wp
    ; trivial      = trivial
    //these are new
    ; get  = (fun _ n0 -> Some n0, n0), get_cps_type
    ; raise = (fun _ h -> None, h + 1), raise_cps_type
}

unfold let lift_pure_stexn (a:Type) (wp:pure_wp a) (h0:int) (p:post a) = wp (fun a -> p (Some a, h0))
sub_effect PURE ~> StateExn = lift_pure_stexn

effect StExn (a:Type) (req:pre) (ens:int -> option a -> int -> GTot Type0) =
       StateExn a
         (fun (h0:int) (p:post a) -> req h0 /\ (forall (r:option a) (h1:int). (req h0 /\ ens h0 r h1) ==> p (r, h1))) (* WP *)

effect S (a:Type) =
       StateExn a (fun h0 p -> forall x. p x)

//let f = StateExn.reflect (fun h0 -> None, h0); this rightfully fails, since StateExn is not reflectable
val div_intrinsic : i:nat -> j:int -> StExn int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> match x with
			| None -> h0 + 1 = h1 /\ j=0
			| Some z -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0 then StateExn.raise int
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
  if j=0 then StateExn.raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) 0 with
         | None, 1 -> j = 0
	 | Some z, 0 -> j <> 0 /\ z = i / j) = ()

val try_div': i:nat -> j:nat -> Tot (repr int (fun h0 post ->
		       if j = 0
		       then post (Some 0, h0 + 1)
                       else post (Some (i / j), h0)))
let try_div' i j h0 =
     match reify (div_intrinsic i j) h0 with
     | None, h1 -> assert (h0 + 1 = h1); assert (j = 0); Some 0, h1
     | Some x, h1 -> assert (x = i / j); assert (h0 = h1); Some x, h1

val try_div: i:nat -> j:nat -> StExn int
  (requires (fun h -> True))
  (ensures (fun h0 x h1 -> if j=0
		        then x=Some 0 /\ h1 = h0 + 1
			else x=Some (i/j) /\ h0 = h1))
let try_div i j = StateExn.reflect (try_div' i j)

//unfortunately, this yet doesn't work with type-inference:
(*
let try_div i j =
  StateExn.reflect (fun h0 -> match reify (div_intrinsic i j) h0 with
			      | None, h1 -> Some 0, h1
			      | x -> x)
*)

//Also, tried packaging up this reflect/reify pattern into a handler
val handle: #a:Type0 -> #wp:wp a -> $f:(unit -> StateExn a wp)
	  -> def:a
	  -> StateExn a (fun h0 post ->
			  wp h0 (fun (x, h1) ->
				   match x with
				   | None -> post (Some def, h1)
				   |  _ -> post (x, h1)))
//but this fails to verify because the WPs are too abstract,
//e.g., we don't have any monotonicity property on them
(* let handle #a #wp f def =  *)
(*   admit(); *)
(*   StateExn.reflect (fun h0 ->  *)
(*     admit(); *)
(*      match reify (f ()) h0 with  *)
(*      | None, h1 -> Some def, h1 *)
(*      | Some x, h1 -> Some x, h1) *)


(* //Another attempt: *)
(* val handle2: #a:Type0 -> #req:pre -> #ens:(int -> option a -> int -> GTot Type0)  *)
(*           -> $f:(unit -> StExn a req ens) *)
(*           -> def:a  *)
(*           -> StExn a req (fun h0 x h1 ->  *)
(*                           match x with  *)
(*                           | None -> False *)
(*                           | Some z -> (ens h0 None h1 /\ z=def) \/ ens h0 x h1) *)
(* #set-options "--debug StExn.Handle --debug_level HACK!"			   *)
(* let handle2 #a #req #ens f def = *)
(*   StateExn.reflect (fun h0 -> *)
(*      match reify (f ()) h0 with *)
(*      | None, h1 -> Some def, h1 *)
(*      | Some x, h1 -> Some x, h1) *)

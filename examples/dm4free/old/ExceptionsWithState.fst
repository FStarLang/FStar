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
module ExceptionsWithState
let pre = int -> Type0
let post (a:Type) = option (a * int) -> Type0
let wp (a:Type) = int -> post a -> Type0
unfold let return_wp (a:Type) (x:a) (n0:int) (post:post a) =
  forall y. y==Some (x, n0) ==> post y

//working around #517 by adding an explicit 'val'
unfold val bind_wp : r:range -> (a:Type) -> (b:Type) -> (f:wp a) -> (g:(a -> Tot (wp b))) -> Tot (wp b)
let bind_wp r a b f g =
    fun n0 post -> f n0 (function
        | None -> post None
	| Some (x, n1) -> g x n1 post)

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
     (forall x. p x)
unfold let trivial       (a:Type)
                            (wp:wp a) =
     (forall h0. wp h0 (fun r -> True))

//new
let repr (a:Type) (wp:wp a) =
    n0:int -> PURE (option (a * int)) (wp n0)

unfold val bind: (a:Type) -> (b:Type) -> (wp0:wp a)
		 -> (f:repr a wp0)
		 -> (wp1:(a -> Tot (wp b)))
		 -> (g:(x:a -> Tot (repr b (wp1 x))))
		 -> Tot (repr b (bind_wp range_0 a b wp0 wp1))
let bind a b wp0 f wp1 g
  = fun n0 -> admit(); match f n0 with
		    | None -> None
		    | Some (x, n1) -> g x n1
let return (a:Type) (x:a)
  : repr a (return_wp a x)
  = fun n0 -> Some (x, n0)

//Just raise; get and put are just lifted from IntST.STATE
val raise : a:Type0 -> Tot (repr a (fun h0 (p:post a) -> p None))
let raise a (h:int) = None

let raise_cps_type = a:Type0 -> Tot (repr a (fun h0 (p:post a) -> p None))

reifiable reflectable new_effect {
  ExnState : a:Type -> wp:wp a -> Effect
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
     ; raise = (fun _ _ -> None), raise_cps_type
}

unfold let lift_pure_exnst (a:Type) (wp:pure_wp a) (h0:int) (p:post a) = wp (fun a -> p (Some (a, h0)))
sub_effect PURE ~> ExnState = lift_pure_exnst

let lift_state_exnst_wp (a:Type) (wp:IntST.wp a) (h0:int) (p:post a) = wp h0 (function (x, h1) -> p (Some (x, h1)))
let lift_state_exnst (a:Type) (wp:IntST.wp a) (f:IntST.repr a wp)
  : (repr a (lift_state_exnst_wp a wp))
  = fun h0 -> admit(); Some (f h0)

sub_effect IntST.STATE ~> ExnState {
  lift_wp = lift_state_exnst_wp;
  lift = lift_state_exnst
}

effect ExnSt (a:Type) (req:pre) (ens:int -> option (a * int) -> GTot Type0) =
       ExnState a
         (fun (h0:int) (p:post a) -> req h0 /\ (forall r. (req h0 /\ ens h0 r) ==> p r))

effect S (a:Type) =
       ExnState a (fun h0 p -> forall x. p x)

val div_intrinsic : i:nat -> j:int -> ExnSt int
  (requires (fun h -> True))
  (ensures (fun h0 x -> match x with
		     | None -> j=0
		     | Some (z, h1) -> h0 = h1 /\ j<>0 /\ z = i / j))
let div_intrinsic i j =
  if j=0
  then (IntST.incr (); ExnState.raise int) //despite the incr (implicitly lifted), the state is reset
  else i / j

reifiable let div_extrinsic (i:nat) (j:int) : S int =
  if j=0 then ExnState.raise int
  else i / j

let lemma_div_extrinsic (i:nat) (j:int) :
  Lemma (match reify (div_extrinsic i j) 0 with
         | None -> j = 0
	 | Some (z, 0) -> j <> 0 /\ z = i / j) = ()

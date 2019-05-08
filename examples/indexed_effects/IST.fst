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
module IST

(* 
   A proof-of-concept example of indexed effects (the state-indexed STATE effect) encoded using standard F* WP calculi 
*)


(* The state-indexed STATE effect; defined explicitly due to the pi-types used in it *)

//s is at universe level 0 because otherwise sub_effect complains about being too universe polymorphic


let st_pre   (s:Type0) = s -> GTot Type0
let st_post' (s:Type0) (a:Type) (pre:Type) = a -> (_:s{pre}) -> GTot Type0
let st_post  (s:Type0) (a:Type) = st_post_h' s a True
let st_wp    (a:Type) = s:Type0 -> st_post_h s a -> Tot (st_pre_h s)

unfold 
let st_return  (a:Type) (x:a) (s:Type0) (post:st_post s a) 
  = post x

unfold 
let st_bind_wp (r1:range) (a:Type) (b:Type)
               (wp1:st_wp a) (wp2:(a -> GTot (st_wp b)))
               (s:Type0) (post:st_post s b) (s0:s) 
  = wp1 s (fun a s1 -> wp2 a s post s1) s0

unfold 
let st_if_then_else (a:Type) (p:Type)
                    (wp_then:st_wp a) (wp_else:st_wp a)
                    (s:Type0) (post:st_post_h s a) (s0:s) 
  = l_ITE p (wp_then s post s0) (wp_else s post s0)

unfold 
let st_ite_wp (a:Type) (wp:st_wp a)
              (s:Type0) (post:st_post s a) (s0:s) 
  = forall (k:st_post s a).
	      (forall (x:a) (s1:s).{:pattern (guard_free (k x s1))} post x s1 ==> k x s1)
	      ==> wp s k s0

unfold 
let st_stronger (a:Type) (wp1:st_wp a)
                (wp2:st_wp a)
  = forall (s:Type0) (post:st_post s a) (s0:s). wp1 s post s0 ==> wp2 s post s0

unfold 
let st_close_wp (a:Type) (b:Type)
                (wp:(b -> GTot (st_wp a)))
                (s:Type0) (post:st_post s a) (s0:s) 
  = (forall (x:b). wp x s post s0)

unfold 
let st_assert_p (a:Type) (p:Type)
                (wp:st_wp a)
                (s:Type0)
                (q:st_post s a) (s0:s) 
  = p /\ wp s q s0

unfold 
let st_assume_p (a:Type) (p:Type)
                (wp:st_wp a)
                (s:Type0)
                (q:st_post s a) (s0:s) 
  = p ==> wp s q s0

unfold 
let st_null_wp (a:Type) (s:Type0) 
               (p:st_post s a) (s0:s) 
  = forall (x:a) (s0:s). p x s0

unfold 
let st_trivial (a:Type) (wp:st_wp a) 
  = forall s s0. wp s (fun r s1 -> True) s0

new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
  with 
     //repr         = s:Type0 -> s -> M (a * s) //pi-types currently not supported by DM4F
       return_wp    = st_return
     ; bind_wp      = st_bind_wp
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite_wp
     ; stronger     = st_stronger
     ; close_wp     = st_close_wp
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null_wp
     ; trivial      = st_trivial
}


(* Standard lifting *)

unfold 
let lift_div_st (a:Type) (wp:pure_wp a) 
                (s:Type0) (p:st_post s a) (s0:s) 
  = wp (fun x -> p x s0)
sub_effect DIV ~> STATE = lift_div_st


(* Non-indexed ST WPs and syntactic sugar for writing effect indices *)

let st_wp'   (a:Type) (s:Type0) = st_post s a -> st_pre s

unfold
let (><) (#a:Type) (s:Type0) (wp:st_wp' a s) : st_wp a
  = fun s' post s0 -> s == s' /\ wp post s0


(* Standard, but now state-indexed get and put actions *)

assume val get (#s:Type0) (_:unit) : STATE s (s >< (fun p s0 -> p s0 s0))

assume val put (#s:Type0) (s1:s) : STATE unit (s >< (fun p s0 -> p () s1))


(* Some sample code *)

let f () : STATE unit (int >< (fun p s0 -> p () s0))
  = () // without setting unfold for lift_div_st this fails

let g (i:nat{i > 0}) 
  : STATE int (int >< (fun p s0 -> forall k . k > s0 ==> p s0 k))
  = let j = get () in put (i + j); j

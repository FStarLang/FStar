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
module IEXN

(* 
   A proof-of-concept example of indexed effects (the allowed exceptions indexed EXN effect) encoded using standard F* WP calculi 
*)


(* The allowed exceptions indexed EXN effect; defined explicitly rather than via DM4F due to the pi-types used in it *)

let exns = FStar.GSet.set exn

noeq type result (a:Type) =        (* we cannot make result explicitly dependent on any given set of exceptions es  *)
  | V   : v:a -> result a          (* because we cannot subtype postconditions based on FStar.GSet.subset relation; *)
  | E   : e:exn -> result a        (* doing so would cause the definition of (><) to not typecheck any more;        *)
                                   (* but we would need such dependency (and subtyping) for correct reify/reflect   *)

let iex_pre  = Type0
let iex_post' (a:Type) (pre:Type) = (_:result a{pre}) -> GTot Type0
let iex_post  (a:Type) = iex_post' a True
let iex_wp    (a:Type) = es:exns -> iex_post a -> GTot ex_pre

unfold 
let iex_return   (a:Type) (x:a) (es:exns) (p:iex_post a) : GTot Type0 = p (V x)

unfold 
let iex_bind_wp (r1:range) (a:Type) (b:Type)
      (wp1:iex_wp a)
      (wp2:(a -> GTot (iex_wp b))) (es:exns) (p:iex_post b)
  : GTot Type0 =
  forall (k:iex_post b).
     (forall (rb:result b).{:pattern (guard_free (k rb))} p rb ==> k rb)
     ==> (wp1 es (function
                  | V ra1 -> wp2 ra1 es k
                  | E e -> k (E e)))

unfold 
let iex_ite_wp (a:Type) (wp:iex_wp a) (es:exns) (post:iex_post a) =
  forall (k:iex_post a).
     (forall (rb:result a).{:pattern (guard_free (k rb))} post rb ==> k rb)
     ==> wp es k

unfold 
let iex_if_then_else (a:Type) (p:Type) 
      (wp_then:iex_wp a) (wp_else:iex_wp a) 
      (es:exns) (post:iex_post a) =
   l_ITE p
       (wp_then es post)
       (wp_else es post)
       
unfold 
let iex_stronger (a:Type) (wp1:iex_wp a) (wp2:iex_wp a) =
  forall (es:exns) (p:iex_post a). wp1 es p ==> wp2 es p

unfold 
let iex_close_wp (a:Type) (b:Type) 
      (wp:(b -> GTot (iex_wp a))) (es:exns) (p:iex_post a) = 
  forall (x:b). wp x es p

unfold 
let iex_assert_p (a:Type) (q:Type) 
      (wp:iex_wp a) (es:exns) (p:iex_post a) = 
  q /\ wp es p

unfold 
let iex_assume_p (a:Type) (q:Type) 
      (wp:iex_wp a) (es:exns) (p:iex_post a) = 
  q ==> wp es p

unfold 
let iex_null_wp (a:Type) (es:exns) (p:iex_post a) = 
  forall (r:result a). p r

unfold 
let iex_trivial (a:Type) (wp:iex_wp a) = 
  forall es . wp es (fun r -> True)

new_effect {
  IEXN : result:Type -> wp:iex_wp result -> Effect
  with
  //repr         = e:exns -> M (result a) //pi-types currently not supported by DM4F
    return_wp    = iex_return
  ; bind_wp      = iex_bind_wp
  ; if_then_else = iex_if_then_else
  ; ite_wp       = iex_ite_wp
  ; stronger     = iex_stronger
  ; close_wp     = iex_close_wp
  ; assert_p     = iex_assert_p
  ; assume_p     = iex_assume_p
  ; null_wp      = iex_null_wp
  ; trivial      = iex_trivial
}


(* Standard lifting *)

unfold 
let lift_div_iexn (a:Type) (wp:pure_wp a) (es:exns) (p:iex_post a) = 
  wp (fun a -> p (V a))
  
sub_effect DIV ~> IEXN = lift_div_iexn

let iex_wp' (a:Type) (es:exns) 
  = iex_post a -> Tot iex_pre


(* Non-indexed EXN WPs and syntactic sugar for writing effect indices *)

unfold
let (><) (#a:Type) (es:exns) (wp:iex_wp' a es) : iex_wp a
  = fun es' post -> FStar.GSet.subset es es' /\ wp post


(* Standard, but now state-indexed raise actions *)

assume val raise (#a:Type) (#es:exns) (e:exn{FStar.GSet.mem e es}) : IEXN a (es >< (fun p -> p (E e)))


(* Some sample code *)

assume val exception1 : exn
assume val exception2 : exn

let f () : IEXN unit ((FStar.GSet.empty) 
                      >< 
                      (fun p -> p (V ())))
  = ()

let g () : IEXN unit ((FStar.GSet.union (FStar.GSet.singleton exception1) ((FStar.GSet.singleton exception2))) 
                      >< 
                      (fun p -> p (E exception1)))
  = raise #_ #(FStar.GSet.singleton exception1) exception1

let h (b:bool) : IEXN unit ((FStar.GSet.union (FStar.GSet.singleton exception1) ((FStar.GSet.singleton exception2))) 
                            >< 
                            (fun p -> forall r . p r))
  = if b then () else raise #_ #(FStar.GSet.singleton exception2) exception2




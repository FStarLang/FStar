module IMST

(* A proof-of-concept example of indexed effects (the state-and-preorder indexed MST effect) encoded using standard F* WP calculi *)

open FStar.Preorder

module W = FStar.Monotonic.Witnessed

(* The state-and-preorder indexed MST effect; defined explicitly due to the pi-types used in it *)

//s is at universe level 0 because otherwise sub_effect complains about being too universe polymorphic

let st_post (s:Type0) (a:Type) = a -> s -> Type0
let st_wp   (a:Type)           = s:Type0 -> (preorder s) -> s -> st_post s a -> Type0

unfold
let st_return (a:Type) (x:a) (s:Type0) (rel:preorder s) (s0:s) (p:st_post s a) 
  = forall v. v == x ==> p v s0

unfold
let st_bind (r:range) (a:Type) (b:Type)
            (wp1:st_wp a) (wp2: (a -> Tot (st_wp b))) : st_wp b
  = fun s rel s0 p -> wp1 s rel s0 (fun x s1 -> wp2 x s rel s1 p)

unfold
let st_if_then_else (a:Type) (p:Type) 
                      (wp_then:st_wp a) (wp_else:st_wp a) (s:Type0) (rel:preorder s) (s0:s) (post:st_post s a)
  = l_ITE p (wp_then s rel s0 post) (wp_else s rel s0 post)

unfold
let st_ite (a:Type) (wp:st_wp a) (s:Type0) (rel:preorder s) (s0:s) (post:st_post s a) =
  wp s rel s0 post

unfold
let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall s rel s0 p. wp1 s rel s0 p ==> wp2 s rel s0 p

unfold
let st_close (a:Type) (b:Type) 
             (wp:(b -> GTot (st_wp a))) (s:Type0) (rel:preorder s) (s0:s) (p:st_post s a) =
  forall x. wp x s rel s0 p

unfold
let st_assert_p (a:Type) (p:Type) 
                (wp:st_wp a) (s:Type0) (rel:preorder s) (s0:s) (q:st_post s a) =
  p /\ wp s rel s0 q

unfold
let st_assume_p (a:Type) (p:Type) 
                (wp:st_wp a) (s:Type0) (rel:preorder s) (s0:s) (q:st_post s a) =
  p ==> wp s rel s0 q

unfold
let st_null (a:Type) (s:Type0) (rel:preorder s) (s0:s) (p:st_post s a) =
  forall x s1. p x s1

unfold
let st_trivial (a:Type) (wp:st_wp a) =
  forall s rel s0. wp s rel s0 (fun _ _ -> True)

new_effect {
  IMST : result:Type -> wp:st_wp result -> Effect
  with 
     //repr         = s:Type0 -> s -> M (a * s) //pi-types currently not supported by DM4F
       return_wp    = st_return
     ; bind_wp      = st_bind
     ; if_then_else = st_if_then_else
     ; ite_wp       = st_ite
     ; stronger     = st_stronger
     ; close_wp     = st_close
     ; assert_p     = st_assert_p
     ; assume_p     = st_assume_p
     ; null_wp      = st_null
     ; trivial      = st_trivial
}


(* Standard lifting *)

let lift_div_imst (a:Type) (wp:pure_wp a) (s:Type0) (rel:preorder s) (s0:s) (p:st_post s a) = wp (fun x -> p x s0)
sub_effect DIV ~> IMST = lift_div_imst


(* Non-indexed MST WPs and syntactic sugar for writing effect indices *)

let st_wp'   (a:Type) (s:Type0) = s -> st_post s a -> Type0

unfold
let (><) (#a:Type) (sr:(s:Type0 & preorder s)) (wp:st_wp' a (dfst sr)) : st_wp a
  = fun s rel s0 post -> s == dfst sr /\ (forall x y . rel x y <==> dsnd sr x y) /\ wp s0 post


(* Standard, but now state-and-preorder indexed get, put, witness, and recall actions *)

assume val get (#s:Type0) (#rel:preorder s) (_:unit) : IMST s ((|s , rel|) >< (fun s0 p -> p s0 s0))

assume val put (#s:Type0) (#rel:preorder s) (s1:s) : IMST unit ((|s , rel|) >< (fun s0 p -> rel s0 s1 /\ p () s1))

let witnessed (#s:Type) (#rel:preorder s) (p:predicate s) :Type0 = W.witnessed rel p

assume val witness (#s:Type) (#rel:preorder s) (q:predicate s) 
  : IMST unit ((|s , rel|) >< (fun s0 p -> stable q rel /\ q s0 /\ (witnessed #s #rel q ==> p () s0)))
  
assume val recall (#s:Type) (#rel:preorder s) (q:predicate s) 
  : IMST unit ((|s , rel|) >< (fun s0 p -> stable q rel /\ witnessed #s #rel q /\ (q s0 ==> p () s0)))




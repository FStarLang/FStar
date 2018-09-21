module FStar.IMST

open FStar.Preorder

module W = FStar.Monotonic.Witnessed

(* The state-and-preorder indexed MST effect; defined explicitly rather than via DM4F due to the pi-types used in it *)

//s is at a fixed universe level (here #u1) because because otherwise sub_effect complains about being too universe polymorphic

let st_pre   (s:Type u#1) = s -> GTot Type0
let st_post' (s:Type u#1) (a:Type) (pre:Type) = a -> (_:s{pre}) -> GTot Type0
let st_post  (s:Type u#1) (a:Type) = st_post_h' s a True
let st_wp    (a:Type) = s:Type u#1 -> (preorder s) -> st_post_h s a -> Tot (st_pre_h s)


unfold
let st_return (a:Type) (x:a) (s:Type u#1) (rel:preorder s) (post:st_post s a) (s0:s)
  = forall v. v == x ==> post v s0

unfold
let st_bind (r:range) (a:Type) (b:Type)
            (wp1:st_wp a) (wp2: (a -> Tot (st_wp b))) 
            (s:Type u#1) (rel:preorder s) (post:st_post s b) (s0:s) 
  = wp1 s rel (fun x s1 -> wp2 x s rel post s1) s0

unfold
let st_if_then_else (a:Type) (p:Type) 
                    (wp_then:st_wp a) (wp_else:st_wp a) 
                    (s:Type u#1) (rel:preorder s) (post:st_post s a) (s0:s)
  = l_ITE p (wp_then s rel post s0) (wp_else s rel post s0)

unfold
let st_ite (a:Type) (wp:st_wp a) (s:Type u#1) (rel:preorder s) (post:st_post s a) (s0:s) 
  = forall (k:st_post s a).
	      (forall (x:a) (s1:s).{:pattern (guard_free (k x s1))} post x s1 ==> k x s1)
	      ==> wp s rel k s0

unfold
let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) 
  = forall (s:Type u#1) (rel:preorder s) (p:st_post s a) (s0:s) . wp1 s rel p s0 ==> wp2 s rel p s0

unfold
let st_close (a:Type) (b:Type) (wp:(b -> GTot (st_wp a))) 
             (s:Type u#1) (rel:preorder s) (p:st_post s a) (s0:s) 
  = forall x. wp x s rel p s0

unfold
let st_assert_p (a:Type) (p:Type) (wp:st_wp a) 
                (s:Type u#1) (rel:preorder s) (q:st_post s a) (s0:s)
  = p /\ wp s rel q s0

unfold
let st_assume_p (a:Type) (p:Type) (wp:st_wp a) 
                (s:Type u#1) (rel:preorder s) (q:st_post s a) (s0:s)
  = p ==> wp s rel q s0

unfold
let st_null (a:Type) (s:Type u#1) (rel:preorder s) (p:st_post s a) (s0:s)
  = forall x s1. p x s1

unfold
let st_trivial (a:Type) (wp:st_wp a) 
  = forall s rel s0. wp s rel (fun _ _ -> True) s0

new_effect {
  IMST : result:Type -> wp:st_wp result -> Effect
  with 
     //repr         = s:Type0 -> preorder s -> s -> M (a * s) // - pi-types currently not supported by DM4F
     
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

unfold 
let lift_div_imst (a:Type) (wp:pure_wp a) (s:Type u#1) 
                  (rel:preorder s) (post:st_post s a) (s0:s) 
  = wp (fun x -> post x s0)
sub_effect DIV ~> IMST = lift_div_imst


(* Non-indexed MST WPs and syntactic sugar for writing effect indices *)

let st_wp' (a:Type) (s:Type u#1) 
  = st_post s a -> Tot (st_pre s)

unfold
let index (#a:Type) (s:Type u#1) (rel: preorder s) (wp:st_wp' a s) : st_wp a
  = fun s' rel' post s0 -> s' == s /\ (forall x y . rel x y <==> rel' x y) /\ wp post s0


(* Standard, but now state-and-preorder indexed get, put, witness, and recall actions *)

assume val get (#s:Type u#1) (#rel:preorder s) (_:unit) : IMST s (index s rel (fun p s0 -> p s0 s0))

assume val put (#s:Type u#1) (#rel:preorder s) (s1:s) : IMST unit (index s rel (fun p s0 -> rel s0 s1 /\ p () s1))

let witnessed (#s:Type u#1) (#rel:preorder s) (p:predicate s) : Type0 = W.witnessed rel p

assume val witness (#s:Type u#1) (#rel:preorder s) (q:predicate s) 
  : IMST unit (index s rel (fun p s0 -> stable q rel /\ q s0 /\ (witnessed #s #rel q ==> p () s0)))
  
assume val recall (#s:Type u#1) (#rel:preorder s) (q:predicate s) 
  : IMST unit (index s rel (fun p s0 -> stable q rel /\ witnessed #s #rel q /\ (q s0 ==> p () s0)))

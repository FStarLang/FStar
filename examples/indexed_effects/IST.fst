module IST

(* 
   A proof-of-concept example of indexed effects (the state-indexed STATE effect) encoded using standard F* WP calculi 
*)


(* The state-indexed STATE effect; defined explicitly due to the pi-types used in it *)

//s is at universe level 0 because otherwise sub_effect complains about being too universe polymorphic

let st_post (s:Type0) (a:Type) = a -> s -> Type0
let st_wp   (a:Type)           = s:Type0 -> s -> st_post s a -> Type0

unfold
let st_return (a:Type) (x:a) (s:Type0) (s0:s) (p:st_post s a) 
  = forall v. v == x ==> p v s0

unfold
let st_bind (r:range) (a:Type) (b:Type)
            (wp1:st_wp a) (wp2: (a -> Tot (st_wp b))) : st_wp b
  = fun s s0 p -> wp1 s s0 (fun x s1 -> wp2 x s s1 p)

unfold
let st_if_then_else (a:Type) (p:Type) 
                      (wp_then:st_wp a) (wp_else:st_wp a) (s:Type0) (s0:s) (post:st_post s a)
  = l_ITE p (wp_then s s0 post) (wp_else s s0 post)

unfold
let st_ite (a:Type) (wp:st_wp a) (s:Type0) (s0:s) (post:st_post s a) =
  wp s s0 post

unfold
let st_stronger (a:Type) (wp1:st_wp a) (wp2:st_wp a) =
  forall s s0 p. wp1 s s0 p ==> wp2 s s0 p

unfold
let st_close (a:Type) (b:Type) 
               (wp:(b -> GTot (st_wp a))) (s:Type0) (s0:s) (p:st_post s a) =
  forall x. wp x s s0 p

unfold
let st_assert_p (a:Type) (p:Type) 
                  (wp:st_wp a) (s:Type0) (s0:s) (q:st_post s a) =
  p /\ wp s s0 q

unfold
let st_assume_p (a:Type) (p:Type) 
                  (wp:st_wp a) (s:Type0) (s0:s) (q:st_post s a) =
  p ==> wp s s0 q

unfold
let st_null (a:Type) (s:Type0) (s0:s) (p:st_post s a) =
  forall x s1. p x s1

unfold
let st_trivial (a:Type) (wp:st_wp a) =
  forall s s0. wp s s0 (fun _ _ -> True)

new_effect {
  STATE : result:Type -> wp:st_wp result -> Effect
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

let lift_div_st (a:Type) (wp:pure_wp a) (s:Type0) (s0:s) (p:st_post s a) = wp (fun x -> p x s0)
sub_effect DIV ~> STATE = lift_div_st


(* Non-indexed ST WPs and syntactic sugar for writing effect indices *)

let st_wp'   (a:Type) (s:Type0) = s -> st_post s a -> Type0

unfold
let (><) (#a:Type) (s:Type0) (wp:st_wp' a s) : st_wp a
  = fun s' s0 post -> s == s' /\ wp s0 post


(* Standard, but now state-indexed get and put actions *)

assume val get (#s:Type0) (_:unit) : STATE s (s >< (fun s0 p -> p s0 s0))

assume val put (#s:Type0) (s1:s) : STATE unit (s >< (fun s0 p -> p () s1))


(* Some sample code *)

let f (i:int) : STATE int (int >< (fun s0 p -> p s0 (s0 + i)))
  = let j = get () in put (i + j) ; j

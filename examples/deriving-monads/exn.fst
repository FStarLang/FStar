module Deriving.Exn

effect P (a:Type) (wp:PureWP a) = PURE a wp wp

type exn

type result: Type -> Type =
  | V: #a:Type -> v:a   -> result a
  | E: #a:Type -> e:exn -> result a

kind Pre           = Type
kind Post (a:Type) = result a -> Type
kind WP (a:Type)   = Post a   -> Pre

type DExn (a:Type) (wp:WP a) = unit -> P (result a) (fun 'p -> wp 'p)

opaque type implies_Exn (#a:Type) (p1:Post a) (p2:Post a) = forall x. p1 x ==> p2 x
opaque type monotone_WP (#a:Type) (wp:WP a) =
  forall (p1:Post a) (p2:Post a).{:pattern (wp p1); (wp p2)} implies_Exn p1 p2 ==> (wp p1 ==> wp p2)

val test_monotone1: #a:Type -> wp:WP a -> y:result a
                    -> Lemma (requires (monotone_WP wp /\ wp (fun x -> b2t (x = y))))
                             (ensures (wp (fun x -> True)))
let test_monotone1 (#a:Type) (wp:WP a) (y:result a) = ()

val test_monotone2: #a:Type -> wp:WP a -> p:Type -> q:Type
                    -> Lemma (requires (monotone_WP wp /\ wp (fun x -> p /\ q)))
                             (ensures (wp (fun x -> p)))
let test_monotone2 (a:Type) (wp:WP a) (p:Type) (q:Type) = ()

type wp_return (#a:Type) (x:a) (post:Post a) = post (V x)
val return: #a:Type -> x:a -> Tot (DExn a (wp_return x))
let return (#a:Type) x _ = V x

type wp_bind (#a:Type) (#b:Type) (f:WP a) (g:a -> WP b) : WP b =
  fun (post:Post b) -> f (fun r -> (is_E r ==> post (E #b (E.e r))) /\
                                   (is_V r ==> (g (V.v r)) post))
val bind: #a:Type -> #b:Type -> #wp1:WP a -> #wp2:(a -> WP b)
          -> f:DExn a wp1{monotone_WP wp1 /\ (forall x. monotone_WP (wp2 x))}
          -> g:(x:a -> Tot (DExn b (wp2 x)))
          -> Tot (DExn b (wp_bind wp1 wp2))
let bind (#a:Type) (#b:Type) (#wp1:WP a) (#wp2: (a -> WP b)) f g (y:unit) =
  let r = f () in
  match r with
    | V x -> g x ()
    | E x -> E #b x

val lemma_return_monotone: a:Type -> x:a -> Lemma (monotone_WP (wp_return #a x))
let lemma_return_monotone x = ()

val lemma_bind_preserves_monotonicity:
  a:Type -> b:Type -> wp1:WP a -> wp2:(a -> WP b)
  -> Lemma (requires (monotone_WP wp1 /\ (forall x. monotone_WP (wp2 x))))
           (ensures (monotone_WP (wp_bind wp1 wp2)))
let lemma_bind_preserves_monotonicity (a:Type) (b:Type) (wp1:WP a) (wp2:a -> WP b) = ()

val lemma_bind_assoc: a:Type -> b:Type -> c:Type
                      -> wp1:WP a
                      -> wp2:(a -> WP b)
                      -> wp3:(b -> WP c)
                      -> Lemma (forall (post:Post c).
                                wp_bind wp1 (fun (x:a) -> wp_bind (wp2 x) wp3) post
                                <==>
                                wp_bind (wp_bind wp1 wp2) wp3 post)
let lemma_bind_assoc (a:Type) (b:Type) (c:Type)
                     (wp1:WP a) (wp2:(a -> WP b)) (wp3:(b -> WP c)) =
  let _ = assert (forall (post:Post c).
                  wp_bind wp1 (fun (x:a) -> wp_bind (wp2 x) wp3) post <==>
                  wp1 (fun (r:result a) -> (is_E r ==> post (E #c (E.e r))) /\
                                           (is_V r ==> wp2 (V.v r) (fun (r':result b) -> (is_E r' ==> post (E #c (E.e r'))) /\
                                                                                         (is_V r' ==> wp3 (V.v r') post))))) in
                                                                                         
  let _ = cut (forall (a:Type) (r:result a{is_E r}) (b:Type). E.e (E #b (E.e r)) = E.e r) in
  
  (*let _ = assert (forall (post:Post c).
                  wp_bind (wp_bind wp1 wp2) wp3 post ==>
                  wp1 (fun (r:result a) -> (is_E r ==> post (E #c (E.e r))) /\
                                           (is_V r ==> wp2 (V.v r) (fun (r':result b) -> (is_E r' ==> post (E #c (E.e r'))) /\
                                                                                         (is_V r' ==> wp3 (V.v r') post))))) in
*)
  admit ()

val lemma_left_unit: a:Type -> b:Type
                     -> x:a
                     -> wp2:(a -> WP b)
                     -> Lemma (forall (post:Post b).
                                   wp_bind (wp_return x) wp2 post
                                   <==>
                                   wp2 x post)
let lemma_left_unit (a:Type) (b:Type) (x:a) (wp2: a -> WP b) = ()

val lemma_right_unit: a:Type -> wp1:WP a
                      -> Lemma (requires (monotone_WP wp1))
                               (ensures (forall (post:Post a).
                                         wp_bind wp1 (wp_return #a) post
                                         <==>
                                         wp1 post))
let lemma_right_unit (a:Type) (wp1:WP a) = ()

opaque type monotone_PureWP (#a:Type) (wp:PureWP a) =
   (forall (p1:PurePost a) (p2:PurePost a).{:pattern (wp p1); (wp p2)}
           (forall x. p1 x ==> p2 x) ==> (wp p1 ==> wp p2))

type wp_lift (#a:Type) (wp:PureWP a) : WP a = (fun (post:Post a) -> wp (fun x -> post (V x)))
val lift: a:Type -> wp:PureWP a -> f:(unit -> P a wp){monotone_PureWP wp} -> Tot (DExn a (wp_lift wp))
let lift 'a 'wp f (y:unit) = V (f ())

val lift_unit: #a:Type -> x:a -> p:Post a
               -> Lemma (wp_return x p <==> wp_lift (pure_return a x) p)
let lift_unit 'a x 'p = ()

val lemma_lift_bind:
  a:Type -> b:Type -> wp1:PureWP a -> wp2:(a -> PureWP b) -> post:Post b
  -> Lemma (requires (monotone_PureWP wp1 /\ (forall x. monotone_PureWP (wp2 x))))
           (ensures  (wp_bind (wp_lift wp1) (fun x -> wp_lift (wp2 x)) post
                      <==>
                      wp_lift (pure_bind_wlp a b wp1 wp2) post))
let lemma_lift_bind 'a 'b 'wp1 'wp2 'post = admit ()


(*--build-config
    options:--split_cases 1;
    other-files:
  --*)

module Deriving.Exn

effect P (a:Type) (wp:PureWP a) = PURE a wp wp

type exn

type result (a:Type) =
  | V: v:a   -> result a
  | E: e:exn -> result a

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

type wp_bind (#a:Type) (#b:Type) (f:WP a) (g:a -> WP b) =
  fun (post:Post b) -> f (fun r -> (is_E r ==> post (E (E.e r))) /\
                                   (is_V r ==> (g (V.v r)) post))
val bind: #a:Type -> #b:Type -> #wp1:WP a -> #wp2:(a -> WP b)
          -> f:DExn a wp1{monotone_WP wp1 /\ (forall x. monotone_WP (wp2 x))}
          -> g:(x:a -> Tot (DExn b (wp2 x)))
          -> Tot (DExn b (wp_bind wp1 wp2))
let bind (#a:Type) (#b:Type) (#wp1:WP a) (#wp2: (a -> WP b)) f g (y:unit) =
  let r = f () in
  match r with
    | V x -> g x ()
    | E x -> E x

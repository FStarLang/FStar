module Bug446

kind WP (a:Type) = STWP_h int a

effect P (a:Type) (wp:PureWP a) = PURE a wp wp

type M (a:Type) (wp:WP a) = 
  i0:int -> P (a * int) (fun 'q -> wp (fun a i -> 'q (a, i)) i0)

val works : #a:Type -> #wp1:WP a -> f:M a wp1 -> Tot bool
let works (#a:Type) (#wp1:WP a) (f:M a wp1) : bool = true

assume val fails : #a:Type -> #b:Type -> #wp1:WP a -> #wp2:WP b ->
                   f:M a wp1 -> g:M a (* <- should be b *) wp2 -> Tot bool

(* Horrible error message: Unknown assertion failed *)

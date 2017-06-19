module Bug446

open FStar.ST

type wP (a:Type) = st_wp_h int a

effect P (a:Type) (wp:pure_wp a) = PURE a wp

type m (a:Type) (wp:wP a) =
  i0:int -> P (a * int) (fun 'q -> wp (fun a i -> 'q (a, i)) i0)

val works : #a:Type -> #wp1:wP a -> f:m a wp1 -> Tot bool
let works (#a:Type) (#wp1:wP a) (f:m a wp1) : bool = true

assume val fails : #a:Type -> #b:Type -> #wp1:wP a -> #wp2:wP b ->
                   f:m a wp1 -> g:m a (* <- should be b *) wp2 -> Tot bool

(* Horrible error message: Unknown assertion failed -- now good *)

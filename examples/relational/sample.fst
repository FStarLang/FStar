module Bijection

opaque type injection (#a:Type) (#b:Type) (f:a -> Tot b) = (forall (x:a) (y:a). f x = f y ==> x = y)
opaque type surjection (#a:Type)(#b:Type) (f:a -> Tot b) = (forall (y:b). (exists (x:a). f x = y))
opaque type bijection (#a:Type) (#b:Type) (f:a -> Tot b) = injection f /\ surjection f
type bij (#a:Type) (#b:Type) = f:(a -> Tot b){bijection f}
opaque type inverses (#a:Type) (#b:Type) (f:a -> Tot b) (g:b -> Tot a) =
   (forall (y:b). f (g y) = y) /\
   (forall (x:a). g (f x) = x)
opaque val lemma_inverses_bij: a:Type -> b:Type -> f:(a -> Tot b) -> g:(b -> Tot a) ->
  Lemma (requires (inverses f g))
        (ensures (bijection f))
let lemma_inverses_bij f g = ()

module Sample
open Bijection

(* sample two random values such that they are related by a bijection f *)
assume val sample : #a:Type -> #b:Type
                    -> f:(a -> Tot b){bijection f}
                    -> Tot (r:(a * b) {snd r = f (fst r)})

(*--build-config
    options:--admit_fsi FStar.Set --z3timeout 5;
    other-files:set.fsi heap.fst st.fst all.fst st2.fst
  --*)

module Bijection

(* Definition of the bijection properties *)
opaque type injection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  (forall (x:a) (y:a). f x = f y ==> x = y)
opaque type surjection (#a:Type)(#b:Type) (f:a -> Tot b) = 
  (forall (y:b). (exists (x:a). f x = y))
opaque type bijection (#a:Type) (#b:Type) (f:a -> Tot b) = 
  injection f /\ surjection f
type bij (#a:Type) (#b:Type) = f:(a -> Tot b){bijection f}

(* giving the inverse function is the best way to prove that a function is a
   bijection *)
opaque type inverses (#a:Type) (#b:Type) (f:a -> Tot b) (g:b -> Tot a) =
   (forall (y:b). f (g y) = y) /\
   (forall (x:a). g (f x) = x)
opaque val lemma_inverses_bij: #a:Type -> #b:Type -> f:(a -> Tot b) 
  -> g:(b -> Tot a) 
  -> Lemma (requires (inverses f g))
           (ensures (bijection f))
let lemma_inverses_bij f g = ()

(* Having bijections in the environment causes serious performance issues
   (#312). Therefore we use the assumed type good_sample_fun. We will show that
   functions are bijections in external lemmas and use the type good_sample_fun
   to control the call to sample. This is safe, as good_sample_fun can only be
   obtained from bijections *)
assume logic type good_sample_fun (#a:Type) (#b:Type) (f:a -> Tot b)
assume val bijection_good_sample_fun : #a:Type -> #b:Type -> f:(a -> Tot b) ->
  Lemma (requires (bijection f))
        (ensures  (good_sample_fun f))
assume val good_sample_fun_bijection : #a:Type -> #b:Type -> f:(a -> Tot b) ->
  Lemma (requires (good_sample_fun f))
        (ensures ((forall (x:a) (y:a). f x = f y ==> x = y)
              /\ (forall (y:b). (exists (x:a). f x = y))))
module Sample
open Bijection
open FStar.Relational
open FStar.Heap
open FStar.Comp

(* sample two random values such that they are related by a bijection f *)
assume val sample : #a:Type -> #b:Type
                    -> f:(a -> Tot b){good_sample_fun f}
                    -> ST2 (rel a  b)
                           (requires (fun h      -> True))
                           (ensures  (fun h r h' -> R.r r = f (R.l r)
                                                 /\ and_irel (rel_map2T equal h h')))

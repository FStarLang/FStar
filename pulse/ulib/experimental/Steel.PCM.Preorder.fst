module Steel.PCM.Preorder
open Steel.PCM
open FStar.Preorder

let induces_preorder #a (p:pcm a) (q:preorder a) =
  forall (x y:a). frame_preserving p x y
         ==> (forall (z:a). compatible p x z ==> q z y)

let preorder_of_pcm #a (p:pcm a) : preorder a =
  fun x y -> forall (q:preorder a). induces_preorder p q ==> q x y

let stability #a (fact:a -> prop) (q:preorder a) (p:pcm a)
  : Lemma
    (requires stable fact q /\
              induces_preorder p q)
    (ensures  stable fact (preorder_of_pcm p))
  = ()

let frame_preserving_is_preorder_respecting #a (p:pcm a) (x y:a)
  : Lemma (requires frame_preserving p x y)
          (ensures (forall z. compatible p x z ==> preorder_of_pcm p z y))
  = ()

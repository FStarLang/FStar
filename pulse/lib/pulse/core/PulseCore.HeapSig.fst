module PulseCore.HeapSig
open FStar.Ghost
open FStar.PCM
module H2 = PulseCore.Heap2
module ST = PulseCore.HoareStateMonad
module CM = FStar.Algebra.CommMonoid

let exists_ #h #a p = h.as_slprop (fun m -> exists (x:a). h.interp (p x) m)
let interp_exists (#h:heap_sig u#h) (#a:Type u#a) (p: a -> h.slprop)
: Lemma (forall m. h.interp (exists_ p) m <==> (exists x. h.interp (p x) m))
= h.interp_as (fun m -> exists (x:a). h.interp (p x) m)

let erase_cm (#a:Type) (c:CM.cm a)
: CM.cm (erased a)
= CM.CM (hide c.unit)
        (fun x y -> hide (c.mult (reveal x) (reveal y)))
        (fun x -> c.identity (reveal x))
        (fun x y z -> c.associativity (reveal x) (reveal y) (reveal z))
        (fun x y -> c.commutativity (reveal x) (reveal y))

let cm_slprop (hs:heap_sig u#h) 
: c:CM.cm (hs.slprop) { c.unit == hs.emp /\ c.mult == hs.star }
= CM.CM hs.emp
        hs.star
        (fun x -> hs.emp_unit x; hs.star_commutative x hs.emp)
        hs.star_associative hs.star_commutative

let cm_e_slprop (hs:heap_sig u#h) = erase_cm (cm_slprop hs)
module Pulse.NondeterministicMonotonicStateMonad
open FStar.Preorder


val nmst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
: Type u#0


val return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: nmst rel a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)
           

let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop


val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:nmst rel a req_f ens_f)
      (g:(x:a -> Dv (nmst rel b (req_g x) (ens_g x))))
: nmst rel b
  (fun s0 -> req_f s0 /\ (forall x s1. ens_f s0 x s1 ==> (req_g x) s1))
  (fun s0 r s2 -> req_f s0 /\ (exists x s1. ens_f s0 x s1 /\ (req_g x) s1 /\ (ens_g x) s1 r s2))
    


val weaken
      (#s:Type u#s)
      (#rel:preorder s)
      (#a:Type u#a)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:req_t s)
      (#ens_g:ens_t s a)
      (f:nmst rel a req_f ens_f)
    : Pure (nmst rel a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)


val flip (#s:Type u#s) (#rel:preorder s) (_:unit)
  : nmst rel bool (fun _ -> True) (fun s0 x s1 -> s0 == s1)


val get (#s:Type u#s) (#rel:preorder s) (_:unit)
  : nmst rel s (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == s0)


val put (#s:Type u#s) (#rel:preorder s) (v:s)
  : nmst rel unit (fun s0 -> rel s0 v /\ True) (fun s0 x s1 -> v == s1)


val witnessed (#s:Type u#s) (p: s -> prop) : Type0


val witness (#s:Type u#s) (#rel:preorder s) (p: s -> prop { stable p rel })
  : nmst rel (witnessed p) (fun s0 -> p s0) (fun s0 x s1 -> s0 == s1)


val recall (#s:Type u#s) (#rel:preorder s) (p: s -> prop) (w:witnessed p) 
  : nmst rel unit (fun s0 -> True) (fun s0 x s1 -> s0 == s1 /\ p s1)

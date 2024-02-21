module PulseCore.PreorderStateMonad
open FStar.Preorder

let req_t (s:Type) = s -> prop
let ens_t (s:Type) (a:Type) = s -> a -> s -> prop

let pst
    (#s:Type u#s)
    (a:Type u#a)
    (rel:preorder s)
    (pre:req_t s)
    (post:ens_t s a)
: Type u#(max a s)
= s0:s { pre s0 }
    -> (
        res:(a & s) {
            post s0 res._1 res._2 /\
            rel s0 res._2
        }
    )

val return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: pst a rel (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)           

val bind
      (#s:Type u#s)
      (#a:Type u#a)
      (#b:Type u#b)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (#req_g:a -> req_t s)
      (#ens_g:a -> ens_t s b)
      (f:pst a rel req_f ens_f)
      (g:(x:a -> pst b rel (req_g x) (ens_g x)))
: pst b rel
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
      (f:pst a rel req_f ens_f)
    : Pure (pst a rel req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

val get (#s:Type u#s) (#rel:preorder s) (_:unit)
  : pst s rel (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == s0)

val put (#s:Type u#s) (#rel:preorder s) (v:s)
  : pst unit rel  (fun s0 -> rel s0 v /\ True) (fun s0 x s1 -> v == s1)
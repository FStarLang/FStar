module PulseCore.MonotonicStateMonad
open FStar.Preorder
// module M = FStar.MSTTotal
module PST = PulseCore.PreorderStateMonad
module W = FStar.Witnessed.Core
val mst (#s:Type u#s)
        (rel:FStar.Preorder.preorder s)
        (a:Type u#a)
        (pre:s -> prop)
        (post:s -> a -> s -> prop)
: Type u#(max a s)

val lift_pst
    (#s:Type u#s)
    (#rel:FStar.Preorder.preorder s)
    (#a:Type u#a)
    (#pre:s -> prop)
    (#post:s -> a -> s -> prop)
    (pst:PST.pst a rel pre post)
: mst rel a pre post

// val of_msttotal (#s:Type u#2) (rel:FStar.Preorder.preorder s)
//                 (a:Type u#a) (pre:s -> prop) (post:s -> a -> s -> prop)
//                 (f:unit -> M.MSTATETOT a s rel pre post)
// : mst rel a pre post

// val to_msttotal (#s:Type u#2) (rel:FStar.Preorder.preorder s)
//                 (a:Type u#a) (pre:s -> prop) (post:s -> a -> s -> prop)
//                 (f:mst rel a pre post)
// : M.MSTATETOT a s rel pre post

val return (#s:Type u#s)
           (#rel:preorder s)
           (#a:Type u#a)
           (x:a)
: mst rel a (fun _ -> True) (fun s0 v s1 -> x == v /\ s0 == s1)
           

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
      (f:mst rel a req_f ens_f)
      (g:(x:a -> mst rel b (req_g x) (ens_g x)))
: mst rel b
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
      (f:mst rel a req_f ens_f)
    : Pure (mst rel a req_g ens_g)
      (requires
        (forall s. req_g s ==> req_f s) /\
        (forall s0 x s1. (req_g s0 /\ ens_f s0 x s1) ==> ens_g s0 x s1))
      (ensures fun _ -> True)

val get (#s:Type u#s) (#rel:preorder s) (_:unit)
  : mst rel s (fun _ -> True) (fun s0 x s1 -> s0 == s1 /\ x == s0)

val put (#s:Type u#s) (#rel:preorder s) (v:s)
  : mst rel unit (fun s0 -> rel s0 v /\ True) (fun s0 x s1 -> v == s1)

val witness (#s:Type u#s) (#rel:preorder s) (p: s -> prop { stable p rel })
  : mst rel (W.witnessed s rel p) (fun s0 -> p s0) (fun s0 x s1 -> s0 == s1)

val recall (#s:Type u#s) (#rel:preorder s) (p: s -> prop) (w:W.witnessed s rel p) 
  : mst rel unit (fun s0 -> True) (fun s0 x s1 -> s0 == s1 /\ p s1)

let mst_aux #s rel a req_f ens_f = 
    x:s { req_f x } -> mst #s rel a (fun s0 -> s0 == x) ens_f

val with_get
      (#s:Type u#s)
      (#a:Type u#a)
      (#rel:preorder s)
      (#req_f:req_t s)
      (#ens_f:ens_t s a)
      (f: mst_aux rel a req_f ens_f)
: mst rel a req_f ens_f

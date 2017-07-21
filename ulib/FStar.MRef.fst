module FStar.MRef
open FStar.Heap
open FStar.ST

open FStar.Preorder
open FStar.DataInvariant

let stable (#a:Type) (p:(a -> Type)) (b:preorder a) = forall x y. p x /\ b x y ==> p y

private let p_pred (#a:Type) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) (p:(a -> Type))
  = fun h -> h `contains` r /\ p (sel h r)

abstract let token (#a:Type) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) (p:(a -> Type){stable p rel})
  = witnessed (p_pred r p)

abstract val take_token: #a:Type -> #inv:data_inv a -> #rel:preorder a -> m:mref a inv rel -> p:(a -> Type){stable p rel}
                         -> ST unit (requires (fun h0 -> p (sel h0 m)))
                                   (ensures (fun h0 _ h1 -> h0==h1 /\ token m p))
let take_token #a #inv #rel m p =
  gst_recall (contains_pred m);
  gst_witness (p_pred m p)

abstract val recall_token: #a:Type -> #inv:data_inv a -> #rel:preorder a -> m:mref a inv rel -> p:(a -> Type){stable p rel}
                           -> ST unit (requires (fun _ ->  token m p))
                                     (ensures (fun h0 _ h1 -> h0==h1 /\ p (sel h1 m)))
let recall_token #a #inv #rel m p = gst_recall (p_pred m p)

abstract val recall: p:(heap -> Type){ST.stable p}
                     -> ST unit (requires (fun _ ->  witnessed p))
                               (ensures (fun h0 _ h1 -> h0 == h1 /\ p h1))
let recall p = gst_recall p

abstract val witness: p:(heap -> Type){ST.stable p}
                      -> ST unit (requires (fun h0 -> p h0))
                                (ensures (fun h0 _ h1 -> h0==h1 /\ witnessed p))
let witness p = gst_witness p

module MRefx

open Heapx
open STx
open Preorder

private let p_pred (#a:Type) (#b:preorder a) (r:mref a b) (p:(a -> Type))
  = fun h -> h `contains` r /\ p (sel h r)

abstract let token (#a:Type) (#b:preorder a) (r:mref a b) (p:(a -> Type){stable p b})
  = witnessed (p_pred r p)

abstract val witness: #a:Type -> #b:preorder a -> m:mref a b -> p:(a -> Type){stable p b}
                         -> ST unit (requires (fun h0 -> p (sel h0 m)))
                                   (ensures (fun h0 _ h1 -> h0==h1 /\ token m p))
let witness #a #b m p =
  gst_recall (contains_pred m);
  gst_witness (p_pred m p)

abstract val recall: #a:Type -> #b:preorder a -> m:mref a b -> p:(a -> Type){stable p b}
                           -> ST unit (requires (fun _ ->  token m p))
                                     (ensures (fun h0 _ h1 -> h0==h1 /\ p (sel h1 m)))
let recall #a #b m p = gst_recall (p_pred m p)

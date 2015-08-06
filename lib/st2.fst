(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../lib;
    other-files:$LIB/set.fsi $LIB/heap.fst $LIB/st.fst
  --*)
module Comp
open Heap
type heap2 = heap * heap

new_effect STATE2 = STATE_h heap2
kind ST2Pre = STPre_h heap2
kind ST2Post (a:Type) = STPost_h heap2 a
effect ST2 (a:Type) (pre:ST2Pre) (post: (heap2 -> ST2Post a)) =
    STATE2 a
      (fun (p:STPost_h heap2 a) (h:heap2) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
      (fun (p:STPost_h heap2 a) (h:heap2) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))           (* WLP *)
effect St2 (a:Type) = ST2 a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  PURE   ~> STATE2 = (fun (a:Type) (wp:PureWP a) (p:ST2Post a) -> (fun h2 -> wp (fun a0 -> p a0 h2)))

type comp (a:Type) (b:Type) (wp0:STWP a) (wp1:STWP b) (p:((a * b) -> heap2 -> Type)) (h2:heap2) =
    wp0 (fun y0 h0 ->
      wp1 (fun y1 h1 -> p (y0, y1) (h0, h1))
      (snd h2))
    (fst h2)

assume val compose2: #a0:Type -> #b0:Type -> #wp0:(a0 -> STWP b0) -> #wlp0:(a0 -> STWP b0)
                  -> #a1:Type -> #b1:Type -> #wp1:(a1 -> STWP b1) -> #wlp1:(a1 -> STWP b1)
                  -> =c0:(x0:a0 -> STATE b0 (wp0 x0) (wlp0 x0))
                  -> =c1:(x1:a1 -> STATE b1 (wp1 x1) (wlp1 x1))
                  -> x0:a0
                  -> x1:a1
                  -> STATE2 (b0 * b1)
                             (comp b0 b1 (wp0 x0) (wp1 x1))
                             (comp b0 b1 (wlp0 x0) (wlp1 x1))

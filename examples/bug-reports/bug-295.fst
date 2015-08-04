module Bug295
type t : Type -> Type

assume val lookupRef: #a:Type -> t a -> GTot a
assume val length : #a:Type -> t a -> Tot nat
assume val index: #a:Type -> s:t a -> i:nat{i < length s} -> Tot a

assume val readIndex :  #a:Type  -> r:t a
  -> i:nat
  -> Pure a
        (requires (True))
        (ensures (fun v->
                  (i < length (lookupRef r)
                   /\ v = index (lookupRef r) i)))

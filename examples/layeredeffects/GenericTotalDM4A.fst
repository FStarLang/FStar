module GenericTotalDM4A

(* This file used to derive a total Dijkstra-monad-for-all layered effect from
   an underlying monad m and an ordered specification monad w.  The layered
   effect and WP index are gone; the underlying monads are kept explicitly. *)

open FStar.Preorder

// m is a monad.
assume val m (a : Type u#a) : Type u#a
assume val m_return (#a : Type) : a -> m a
assume val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b

let return #a (x:a) : m a = m_return x
let bind #a #b (c:m a) (f:a -> m b) : m b = m_bind c f
let (let!) #a #b (c:m a) (f:a -> m b) : m b = bind c f

// w is an ordered specification monad.  It is no longer an effect index, but
// it remains useful as a separate monad related to m by interp.
[@@erasable]
assume val w (a : Type u#a) : Type u#(1 + a)
assume val w_return (#a : Type) : a -> w a
assume val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
assume val stronger : (#a:Type) -> preorder (w a)

let equiv #a (w1 w2 : w a) = w1 `stronger` w2 /\ w2 `stronger` w1

assume val bind_is_monotonic
  (#a #b : Type)
  (w1 w2 : w a) 
  (f1 f2 : a -> w b)
  : Lemma (requires (w1 `stronger` w2 /\ (forall x. f1 x `stronger` f2 x)))
          (ensures (w_bind w1 f1 `stronger` w_bind w2 f2))

// A morphism between the two monads, satisfying the usual laws.
assume val interp (#a : Type) : m a -> w a

assume val interp_ret (#a:Type) (x:a)
  : Lemma (interp (m_return x) `equiv` w_return x)
  
assume val interp_bind (#a #b:Type)
  (c : m a) (f : a -> m b)
  : Lemma (interp (m_bind c f) `equiv` w_bind (interp c) (fun x -> interp (f x)))

let spec_return #a (x:a) : w a = w_return x
let spec_bind #a #b (c:w a) (f:a -> w b) : w b = w_bind c f

let example_m #a #b (c:m a) (f:a -> m b) : m b =
  let! x = c in
  f x

let example_spec #a #b (c:w a) (f:a -> w b) : w b =
  spec_bind c f

let example_interp #a #b (c:m a) (f:a -> m b)
  : Lemma (interp (m_bind c f) `equiv` w_bind (interp c) (fun x -> interp (f x)))
  = interp_bind c f

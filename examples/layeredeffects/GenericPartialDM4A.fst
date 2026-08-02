module GenericPartialDM4A

(* This file used to derive a partial Dijkstra-monad-for-all layered effect.
   The effect declaration and WP index have been removed.  We keep the generic
   underlying monad m, the ordered specification monad w, and a small explicit
   partial monad that carries only a precondition. *)

open FStar.Preorder

// m is a monad.
assume val m (a : Type u#a) : Type u#a
assume val m_return (#a : Type) : a -> m a
assume val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b

let total_return #a (x:a) : m a = m_return x
let total_bind #a #b (c:m a) (f:a -> m b) : m b = m_bind c f

// w is an ordered specification monad.  It is no longer an effect index.
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

assume val interp (#a : Type) : m a -> w a

assume val interp_ret (#a:Type) (x:a)
  : Lemma (interp (m_return x) `equiv` w_return x)
  
assume val interp_bind (#a #b:Type)
  (c : m a) (f : a -> m b)
  : Lemma (interp (m_bind c f) `equiv` w_bind (interp c) (fun x -> interp (f x)))

noeq type partial (a:Type) = {
  pre: prop;
  comp: squash pre -> m a;
}

let return #a (x:a) : partial a =
  { pre = True; comp = (fun _ -> m_return x) }

let bind #a #b (c:partial a) (f:a -> partial b) : partial b =
  { pre = c.pre /\ (forall x. (f x).pre);
    comp = (fun _ ->
      let v = c.comp () in
      m_bind v (fun x -> (f x).comp ())) }

let (let!) #a #b (c:partial a) (f:a -> partial b) : partial b = bind c f

let run #a (c:partial a) (pf:squash c.pre) : m a = c.comp pf

let example_partial #a #b (c:partial a) (f:a -> partial b) : partial b =
  let! x = c in
  f x

let spec_return #a (x:a) : w a = w_return x
let spec_bind #a #b (c:w a) (f:a -> w b) : w b = w_bind c f

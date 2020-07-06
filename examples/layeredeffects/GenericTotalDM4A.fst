module GenericTotalDM4A

open FStar.Tactics
open FStar.Calc
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
open FStar.Preorder

// m is a monad.
assume val m (a : Type u#a) : Type u#a
assume val m_return (#a : Type) : a -> m a
assume val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b

// w is an ordered monad
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

let (<<=) = stronger

// a morphism between them, satisfying appropriate laws
assume val interp (#a : Type) : m a -> w a

assume val interp_ret (#a:Type) (x:a)
  : Lemma (interp (m_return x) `equiv` w_return x)
  
assume val interp_bind (#a #b:Type)
  (c : m a) (f : a -> m b)
  : Lemma (interp (m_bind c f) `equiv` w_bind (interp c) (fun x -> interp (f x)))

let repr (a : Type) (w: w a) = c:(m a){w `stronger` interp c}

let return (a:Type) (x:a) : repr a (w_return x) =
  interp_ret x;
  m_return x

let bind (a : Type) (b : Type)
  (wp_v : w a) (wp_f: a -> w b)
  (v : repr a wp_v) (f : (x:a -> repr b (wp_f x)))
  : repr b (w_bind wp_v wp_f) =
  let r = m_bind v f in
  (* Proof that stronger holds *)
  calc (<<=) {
    w_bind wp_v wp_f;
    <<= { bind_is_monotonic wp_v (interp v) wp_f (fun x -> interp (f x)) (* from the refinement *) }
    w_bind (interp v) (fun x -> interp (f x));
    <<= { interp_bind v f }
    interp (m_bind v f);
  };
  r
  
let subcomp (a:Type) (w1 w2: w a)
  (f : repr a w1)
  : Pure (repr a w2)
         (requires w2 `stronger` w1)
         (ensures fun _ -> True)
  = f

let if_then_else (a : Type) (w1 w2 : w a) (f : repr a w1) (g : repr a w2) (b : bool) : Type =
  repr a (if b then w1 else w2)

total
reifiable
reflectable
layered_effect {
  DM4A : a:Type -> w a -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp; 
       if_then_else = if_then_else
}

let lift_pure_dm4a (a:Type) (f:(eqtype_as_type unit -> Tot a))
  : repr a (w_return (f ()))
  = return _ (f ())

sub_effect PURE ~> DM4A = lift_pure_dm4a

[@@expect_failure] // lift doesn't really work
let test () : DM4A int (w_return 5) = r 5

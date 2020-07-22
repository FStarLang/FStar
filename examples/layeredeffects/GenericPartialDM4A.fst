module GenericPartialDM4A

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

(* Note the #57-like trick *)
let repr (a : Type) (pre:Type0) (w: squash pre -> w a) =
  squash pre -> c:(m a){w () `stronger` interp c}

let return (a:Type) (x:a) : repr a True (fun _ -> w_return x) =
  fun _ ->
    interp_ret x;
    m_return x

let and_elim_2 (s : squash ('p /\ 'q)) : squash 'q = ()
let fa_elim #a #p (s : squash (forall x. p x)) (x:a) : squash (p x) =
  Squash.bind_squash s (fun (f : (forall x. p x)) ->
  Squash.bind_squash f (fun (f : (x:a -> GTot (p x))) ->
  Squash.return_squash (f x)))

let iw_bind (#a : Type) (#b : Type)
  (pre_v : Type0) (pre_f : a -> Type0)
  (wp_v : squash pre_v -> w a) (wp_f: (x:a -> squash (pre_f x) -> w b))
  : squash (pre_v /\ (forall x. pre_f x)) -> w b
  = fun pf -> w_bind (wp_v ()) (fun x -> let pf' = and_elim_2 pf in
                                   let pf'' = fa_elim pf' x in
                                   wp_f x ())

let bind (a : Type) (b : Type)
  (pre_v : Type0) (pre_f : a -> Type0)
  (wp_v : squash pre_v -> w a) (wp_f: (x:a -> squash (pre_f x) -> w b))
  (v : repr a pre_v wp_v) (f : (x:a -> repr b (pre_f x) (wp_f x)))
  : repr b (pre_v /\ (forall x. pre_f x)) (iw_bind pre_v pre_f wp_v wp_f)
  =
  fun (pf : squash (pre_v /\ (forall x. pre_f x))) ->
    let v = v () in
    let _ = and_elim_2 pf in
    assert (forall (x:a). pre_f x) by (exact (nth_binder (-1))); // what the hell? #1948?
    let f x = f x () in
    let r = m_bind v f in
    (* Proof that stronger holds *)
    calc (<<=) {
      w_bind (wp_v ()) (fun x -> wp_f x ());
      <<= { bind_is_monotonic (wp_v ()) (interp v) (fun x -> wp_f x ()) (fun x -> interp (f x)) (* from the refinement *) }
      w_bind (interp v) (fun x -> interp (f x));
      <<= { interp_bind v f }
      interp (m_bind v f);
    };
    r


private
let weaken (t1 t2 : Type) (s : squash t1)
  : Pure (squash t2)
         (requires (t1 ==> t2))
         (ensures (fun _ -> True))
  = ()

let subcomp (a:Type)
  (p1 p2 : Type0)
  (w1 : squash p1 -> w a)
  (w2 : squash p2 -> w a)
  (f : repr a p1 w1)
  : Pure (repr a p2 w2)
         (requires (p2 ==> p1) /\ (forall (pf : squash p2). w2 pf `stronger` w1 (weaken p2 p1 pf)))
         (ensures fun _ -> True)
  = fun _ -> f ()

let if_then_else (a : Type)
  (p1 : Type0) // FIXME: should take a p2 as well
  (w1 : squash p1 -> w a)
  (w2 : squash p1 -> w a)
  (f : repr a p1 w1)
  (g : repr a p1 w2)
  (b : bool)
  : Type
  = repr a p1 (if b then w1 else w2)

total
reifiable
reflectable
layered_effect {
  DM4A : a:Type -> pre:Type0 -> (squash pre -> w a) -> Effect
  with repr         = repr;
       return       = return;
       bind         = bind;
       subcomp      = subcomp; 
       if_then_else = if_then_else
}

let lift_pure_dm4a (a:Type) (wp : pure_wp a) (f:(eqtype_as_type unit -> PURE a wp))
  : Tot (repr a (wp (fun _ -> True)) (fun _ -> w_return (f ())))
  = fun _ -> 
      FStar.Monotonic.Pure.wp_monotonic_pure ();
      let x = f () in
      interp_ret x;
      m_return x

sub_effect PURE ~> DM4A = lift_pure_dm4a

[@@expect_failure [54]] // why?
let test () : DM4A int True (fun _ -> w_return 5) = 5

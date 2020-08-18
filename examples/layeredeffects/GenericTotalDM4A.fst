module GenericTotalDM4A

open FStar.Tactics
open FStar.Calc
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
open FStar.Preorder
open Common

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

assume val stronger_trans : (#a:Type) ->
  (w1 : w a) -> (w2 : w a) -> (w3 : w a) ->
  Lemma (requires (w1 `stronger` w2 /\ w2 `stronger` w3))
        (ensures (w1 `stronger` w3))

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

(* A lift from Tot *)
let lift_tot_dm4a (a:Type) (f:(eqtype_as_type unit -> Tot a))
  : repr a (w_return (f ()))
  = return _ (f ())
sub_effect PURE ~> DM4A = lift_tot_dm4a

(* We cannot in general have a lift from PURE, due to the partiality.
However if we assume that `m` has a zero element plus some structure,
and we use an axiom to *detect* partial computations and lift them
accordingly, we get away with it. This axiom should not be taken
lightly, it will block any lifted computation since this is really
needed at runtime. *)

(* Strong excluded middle in Tot *)
assume val sem : p:Type0-> b:bool{(b <==> p) /\ (b <==> squash p) /\ (b <==> squash (squash p))}

(* A zero in M *)
assume val mzero : #a:Type -> m a

(* Lifting pure WPs to W *)
assume val lift_wp : #a:_ -> (wp : pure_wp a) -> w a

let sat #a (wp : pure_wp a) : Type0 = wp (fun _ -> True)

(* Some properties on lifting *)
assume val lift_wp_mono : #a:Type -> wp1:pure_wp a -> wp2:pure_wp a ->
  Lemma (requires (forall p. wp1 p ==> wp2 p))
        (ensures lift_wp wp1 `stronger` lift_wp wp2)
assume val lift_ret : #a:Type -> x:a ->
  Lemma (lift_wp (pure_return _ x) <<= w_return x)

(* With PredExt the hypothesis is basically that wp is constantly false,
so one could also just state that lift (fun p -> False) `stronger` interp mzero. *)

assume val lift_unsat_wp_mzero : #a:Type -> wp:pure_wp a ->
  Lemma (requires ~(sat wp))
        (ensures lift_wp wp `stronger` interp mzero)

let lift_pure_dm4a (a:Type) (wp:_) (f:(eqtype_as_type unit -> PURE a wp))
  : repr a (lift_wp wp) 
  = 
    if sem (wp (fun _ -> True))
    then begin
      let x : a = Common.elim_pure f (fun _ -> True) in
      assume (pure_monotonic wp); // usual deal...
      lift_wp_mono wp (pure_return _ x);
      lift_ret x;
      stronger_trans (lift_wp wp) (lift_wp (pure_return _ x)) (w_return x);
      return _ x
    end else begin
      lift_unsat_wp_mzero wp;
      mzero
    end

(* Not sure why this lift is accepted in the presence of the other...
looks like a bug *)
sub_effect PURE ~> DM4A = lift_pure_dm4a

// needs mononicity, sigh
[@expect_failure]
let test () : DM4A int (w_return 5) by (dump "") = 5

module AlgForAll

open Common
open FStar.Calc
module WF = FStar.WellFounded
module FE = FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
open LatticeAlg


let pre = state -> Type0
let post (a:Type) = a -> state -> Type0
let st_wp (a:Type) : Type = post a -> pre

let return_wp #a x : st_wp a = fun p s -> p x s 

let bind_wp #a #b (w : st_wp a) (wf : a -> st_wp b)
  : st_wp b
  = fun p s0 -> w (fun y s1 -> wf y p s1) s0

let read_wp : st_wp state = fun p s0 -> p s0 s0

let write_wp : state -> st_wp unit = fun s p _ -> p () s

(* Also doable with handlers *)
let rec interp_as_wp #a (t : repr a [Read;Write]) : st_wp a =
  match t with
  | Return x -> return_wp x
  | Act Read _ k ->
    bind_wp read_wp (fun s -> WF.axiom1 k s; interp_as_wp (k s))
  | Act Write s k ->
    bind_wp (write_wp s) (fun () -> WF.axiom1 k (); interp_as_wp (k ()))
  
// m is a monad.
val m (a : Type u#a) : Type u#a
let m a = repr a [Read;Write]

val m_return (#a : Type) : a -> m a
let m_return x = Return x

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind c f = bind _ _ _ _ c f

val w (a : Type u#a) : Type u#(max 1 a)
let w = st_wp

val w_return (#a : Type) : a -> w a
let w_return = return_wp

val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
let w_bind = bind_wp

val stronger : (#a:Type) -> FStar.Preorder.preorder (w a)
let stronger w1 w2 = forall p s. w1 p s ==> w2 p s

let equiv #a (w1 w2 : w a) = w1 `stronger` w2 /\ w2 `stronger` w1

let bind_is_monotonic
  (#a #b : Type)
  (w1 w2 : w a) 
  (f1 f2 : a -> w b)
  : Lemma (requires (w1 `stronger` w2 /\ (forall x. f1 x `stronger` f2 x)))
          (ensures (w_bind w1 f1 `stronger` w_bind w2 f2))
  = admit ()

let (<<=) = stronger

// a morphism between them, satisfying appropriate laws
val interp (#a : Type) : m a -> w a
let interp = interp_as_wp

val interp_ret (#a:Type) (x:a)
  : Lemma (interp (m_return x) `equiv` w_return x)
let interp_ret x = assert (interp (m_return x) `equiv` w_return x) by (T.compute ())

val interp_bind (#a #b:Type)
  (c : m a) (f : a -> m b)
  : Lemma (interp (m_bind c f) `equiv` w_bind (interp c) (fun x -> interp (f x)))
let interp_bind c f =
  calc equiv {
    interp (m_bind c f);
    equiv { admit() }
    w_bind (interp c) (fun x -> interp (f x));
  }

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

let _get : repr state read_wp =
  let c0 : LatticeAlg.repr state [Read;Write] = LatticeAlg._get in
  let w = interp_as_wp c0 in
  assert_norm (read_wp `stronger` w);
  c0

let get () : DM4A state read_wp =
  DM4A?.reflect _get
  
let _put (s:state) : repr unit (write_wp s) =
  let c0 : LatticeAlg.repr unit [Read;Write] = LatticeAlg._put s in
  let w = interp_as_wp c0 in
  assert_norm (write_wp s `stronger` w);
  c0

let put (s:state) : DM4A unit (write_wp s) =
  DM4A?.reflect (_put s)

let lift_pure_wp (#a:Type) (wp : pure_wp a) : st_wp a =
  fun p s0 -> wp (fun x -> p x s0)
 
let lift_pure_dm4a (a:Type) wp (f:(eqtype_as_type unit -> PURE a wp))
  : Pure (repr a (lift_pure_wp wp)) // can't call f() here, so lift its wp instead
         (requires (wp (fun _ -> True)))
         (ensures (fun _ -> True))
  = 
    let v : a = elim_pure f (fun _ -> True) in
    FStar.Monotonic.Pure.wp_monotonic_pure ();
    assert (forall p. wp p ==> p v); // this is key fact needed for the proof
    assert_norm (stronger (lift_pure_wp wp) (w_return v));
    Return v

sub_effect PURE ~> DM4A = lift_pure_dm4a

[@@expect_failure] // lift doesn't really work
let test () : DM4A int (w_return 5) = r 5

let addx (x:int) : DM4A unit (fun p s0 -> p () (s0+x)) by (T.norm [delta]) =
  let y = get () in
  put (x+y)

let add_via_state (x y : int) : DM4A int (fun p s0 -> p (x+y) s0) by (T.norm [delta]) =
  let o = get () in
  put x;
  addx y;
  let r = get () in
  put o;
  r

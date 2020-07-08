module AlgForAll

open Common
open FStar.Calc
module WF = FStar.WellFounded
module FE = FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality
module W = FStar.WellFounded
module T = FStar.Tactics
open Alg

let pre = state -> Type0
let post (a:Type) = a -> state -> Type0
let st_wp (a:Type) : Type = post a -> pre

unfold
let return_wp #a x : st_wp a = fun p s -> p x s

unfold
let bind_wp #a #b (w : st_wp a) (wf : a -> st_wp b)
  : st_wp b
  = fun p s0 -> w (fun y s1 -> wf y p s1) s0

unfold
let read_wp : st_wp state = fun p s0 -> p s0 s0

unfold
let write_wp : state -> st_wp unit = fun s p _ -> p () s

(* Also doable with handlers *)
let rec interp_as_wp #a (t : repr a [Read;Write]) : st_wp a =
  match t with
  | Return x -> return_wp x
  | Act Read _ k ->
    bind_wp read_wp (fun s -> WF.axiom1 k s; interp_as_wp (k s))
  | Act Write s k ->
    bind_wp (write_wp s) (fun (o:unit) -> WF.axiom1 k o; interp_as_wp (k o))

// m is a monad.
val m (a : Type u#a) : Type u#a
let m a = repr a [Read;Write]

val m_return (#a : Type) : a -> m a
let m_return x = Return x

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind c f = bind _ _ _ _ c f

val w (a : Type u#a) : Type u#(max 1 a)
let w = st_wp

unfold
val w_return (#a : Type) : a -> w a
unfold
let w_return = return_wp

unfold
val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
unfold
let w_bind = bind_wp

(* Bug: defining this as a FStar.Preorder.preorder
causes stupid failures ahead *)
val stronger : (#a:Type) -> w a -> w a -> Type0
let stronger w1 w2 = forall p s. w1 p s ==> w2 p s

let equiv #a (w1 w2 : w a) = w1 `stronger` w2 /\ w2 `stronger` w1

let (<<=) = stronger

// a morphism between them, satisfying appropriate laws
val interp (#a : Type) : m a -> w a
let interp = interp_as_wp

val interp_ret (#a:Type) (x:a)
  : Lemma (interp (m_return x) `equiv` w_return x)
let interp_ret x = assert (interp (m_return x) `equiv` w_return x) by (T.compute ())

let wp_is_monotonic #a (wp : w a) : Type0 =
  forall p1 p2 s0. (forall x s1. p1 x s1 ==> p2 x s1) ==> wp p1 s0 ==> wp p2 s0

let bind_preserves_mon #a #b (wp : w a) (f : a -> w b)
  : Lemma (requires (wp_is_monotonic wp /\ (forall x. wp_is_monotonic (f x))))
          (ensures (wp_is_monotonic (bind_wp wp f)))
  = ()

let rec interp_monotonic #a (c:m a) : Lemma (wp_is_monotonic (interp c)) =
  match c with
  | Return x -> ()
  | Act Read _ k ->
    let aux (x:state) : Lemma (wp_is_monotonic (interp (k x))) =
      WF.axiom1 k x;
      interp_monotonic (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon read_wp (fun x -> interp (k x))
  | Act Write s k ->
    let aux (x:unit) : Lemma (wp_is_monotonic (interp (k x))) =
      WF.axiom1 k x;
      interp_monotonic (k x)
    in
    Classical.forall_intro aux;
    bind_preserves_mon (write_wp s) (fun x -> interp (k x))

let elim_str #a (w1 w2 : w a) (p : post a) (s0:state)
  : Lemma (requires (w1 <<= w2))
          (ensures w1 p s0 ==> w2 p s0)
  = ()

let rec interp_morph #a #b (c : m a) (f : a -> m b) (p:_) (s0:_)
  : Lemma (interp c (fun y s1 -> interp (f y) p s1) s0 == interp (m_bind c f) p s0)
  = match c with
    | Return x -> ()
    | Act Read _ k ->
      let aux (o:state) : Lemma (interp (k o) (fun y s1 -> interp (f y) p s1) s0
                                        == interp (m_bind (k o) f) p s0) =
        WF.axiom1 k o;
        interp_morph (k o) f p s0
      in
      Classical.forall_intro aux

    | Act Write s k ->
      let aux (o:unit) : Lemma (interp (k o) (fun y s1 -> interp (f y) p s1) s
                                        == interp (m_bind (k o) f) p s) =
        WF.axiom1 k o;
        interp_morph (k o) f p s
      in
      Classical.forall_intro aux

    | _ ->
      unreachable ()

val interp_bind (#a #b:Type)
  (c : m a) (f : a -> m b)
  (w1 : w a) (w2 : a -> w b)
  : Lemma (requires w1 <<= interp c /\ (forall x. w2 x <<= interp (f x)))
          (ensures w_bind w1 w2 `stronger` interp (m_bind c f))
let interp_bind #a #b c f w1 w2 =
  let aux (p:post b) (s0:state) : Lemma (w_bind w1 w2 p s0 ==> interp (m_bind c f) p s0) =
    calc (==>) {
      w_bind w1 w2 p s0;
      ==> {}
      w1 (fun y s1 -> w2 y p s1) s0;
      ==> { (* hyp *)}
      interp c (fun y s1 -> w2 y p s1) s0;
      ==> { interp_monotonic c }
      interp c (fun y s1 -> interp (f y) p s1) s0;
      ==> { interp_morph c f p s0 }
      interp (m_bind c f) p s0;
    }
  in
  Classical.forall_intro_2 aux

let repr (a : Type) (w: w a) = c:(m a){w `stronger` interp c}

let return (a:Type) (x:a) : repr a (w_return x) =
  interp_ret x;
  m_return x

let bind (a : Type) (b : Type)
  (wp_v : w a) (wp_f: a -> w b)
  (v : repr a wp_v) (f : (x:a -> repr b (wp_f x)))
  : repr b (w_bind wp_v wp_f) =
  interp_bind v f wp_v wp_f;
  m_bind v f

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
  let c0 : Alg.repr state [Read;Write] = Alg._get in
  let w = interp_as_wp c0 in
  assert_norm (read_wp `stronger` w);
  c0

let get () : DM4A state read_wp =
  DM4A?.reflect _get

let _put (s:state) : repr unit (write_wp s) =
  let c0 : Alg.repr unit [Read;Write] = Alg._put s in
  let w = interp_as_wp c0 in
  assert_norm (write_wp s `stronger` w);
  c0

let put (s:state) : DM4A unit (write_wp s) =
  DM4A?.reflect (_put s)

unfold
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

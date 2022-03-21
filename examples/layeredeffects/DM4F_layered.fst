module DM4F_layered

(* Same as DM4F, but layered over a layered PURE *)
open ID2
open FStar.Tactics
open Common

(* Simulating state effect in DM4F, hopefully doable by a tactic. *)

type post_t st a =
  a -> st -> Type0

type wp0 (st:Type u#0) (a:Type u#ua) : Type u#(max 1 ua) =
  st -> post_t st a -> Type0

let st_monotonic #st #a (w : wp0 st a) : Type0 =
  //forall s0 p1 p2. (forall r. p1 r ==> p2 r) ==> w s0 p1 ==> w s0 p2
  // ^ this version seems to be less SMT-friendly
  forall s0 p1 p2. (forall x s1. p1 x s1 ==> p2 x s1) ==> w s0 p1 ==> w s0 p2

type wp st a = w:(wp0 st a){st_monotonic w}

open FStar.Monotonic.Pure

type repr (a:Type u#ua) (st:Type0) (wp : wp u#ua st a) : Type u#ua =
  s0:st -> ID (a & st) (as_pure_wp (fun p -> wp s0 (curry p)))

unfold
let return_wp (#a:Type) (#st:Type0) (x:a) : wp st a =
  fun s0 p -> p x s0

let return (a:Type) (x:a) (st:Type0) : repr a st (return_wp x) =
  fun s0 -> (x, s0)

unfold
let bind_wp (#a:Type) (#b:Type) (#st:Type0)
  (w1 : wp st a) (w2 : a -> wp st b) : wp st b =
  fun s0 p -> w1 s0 (fun y s1 -> w2 y s1 p)

let squash_lem a : Lemma (a ==> squash a) = ()

let elim_mon #a #st (w : wp st a) (p1 p2 : post_t st a) (s0:st)
 : Lemma (requires (forall x s1. p1 x s1 ==> p2 x s1))
         (ensures w s0 p1 ==> w s0 p2) = ()

(* All of this is needed due to an auto_squash popping up in the VC *)

let wp_squash_lem #a #st (w : wp st a) (p : post_t st a) (s0:st)
  : Lemma (requires w s0 p) (ensures w s0 (fun x y -> squash (p x y)))
  = calc (==>) {
      w s0 p;
      ==> {}
      w s0 (fun x y -> p x y);
      ==> { elim_mon w (fun x y -> p x y) (fun x y -> squash (p x y)) s0 } // grr
      w s0 (fun x y -> squash (p x y));
    }
    
let bind (a:Type) (b:Type) (st:Type0)
  (wp_c : wp st a)
  (wp_f : a -> wp st b)
  (c : repr a st wp_c)
  (f : (x:a -> repr b st (wp_f x)))
: repr b st (bind_wp wp_c wp_f)
   by (explode ();
       let w = nth_binder 3 in
       apply_lemma (`(wp_squash_lem (`#w)));
       dump "")
= fun s0 ->
      let (y, s1) = c s0 in
      f y s1

let ite_wp #a #st (b:bool) (w1 w2 : wp st a) : wp st a =
  fun s0 p -> (b ==> w1 s0 p) /\ ((~b) ==> w2 s0 p)

let if_then_else
  (a:Type)
  (st:Type0)
  (wpf wpg : wp st a)
  (f : repr a st wpf)
  (g : repr a st wpg)
  (b : bool)
  : Type
  = repr a st (ite_wp b wpf wpg)

let stronger
  (#a:Type) (#st:Type0)
  (w1 w2 : wp st a)
  : Type0
  = forall s0 p. w1 s0 p ==> w2 s0 p

let subcomp
  (a:Type)
  (st:Type0)
  (wpf wpg : wp st a)
  (f : repr a st wpf)
  : Pure (repr a st wpg)
         (requires (stronger wpg wpf))
         (ensures (fun _ -> True))
  = f

total
reifiable
reflectable
layered_effect {
  ST : a:Type -> st:Type0 -> wp st a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  if_then_else = if_then_else;
  subcomp = subcomp
}

let pure_monotonic #a (w : pure_wp a) : Type0 =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

let lift_pure_st_wp #a #st (w : pure_wp a) : wp st a =
  assume (pure_monotonic w);
  let r = fun s0 p -> w (fun x -> p x s0) in
  r

//let lift_pure_st a st wp (f : eqtype_as_type unit -> PURE a wp)
//  : Pure (repr a st (lift_pure_st_wp wp))
//         (requires (pure_monotonic wp))
//         (ensures (fun _ -> True))
//  = fun s0 -> (f (), s0)
//
//sub_effect PURE ~> ST = lift_pure_st

let lift_id_st_wp #a #st (w : pure_wp a) : wp st a =
  elim_pure_wp_monotonicity_forall ();
  fun s0 p -> w (fun x -> p x s0)

(* It's odd that I *have* to use the repr here, instead of a thunked
ID a wp as above. *)
let lift_id_st a st wp (f : ID2.repr a wp)
  : repr a st (lift_id_st_wp wp)
  = elim_pure_wp_monotonicity_forall ();
    fun s0 -> (f (), s0)

sub_effect ID ~> ST = lift_id_st

let null #st #a : wp st a =
  fun s0 p -> forall x s1. p x s1

let get #st () : ST st st (fun s0 p -> p s0 s0) =
  ST?.reflect (fun s0 -> (s0, s0))

let put #st (s:st) : ST unit st (fun _ p -> p () s) =
  ST?.reflect (fun _ -> ((), s))

let test () : ST int int null =
  let x = get () in
  put (x + x);
  get () + get ()

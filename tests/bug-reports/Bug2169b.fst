module Bug2169b

open FStar.FunctionalExtensionality
module T = FStar.Tactics

open FStar.Monotonic.Pure


let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
   f ()

val m (a : Type u#a) : Type u#a
let m a = a

val m_return (#a : Type) : a -> m a
let m_return x = x

val m_bind (#a #b : Type) : m a -> (a -> m b) -> m b
let m_bind l f = f l

val w0 (a : Type u#a) : Type u#(max 1 a)
let w0 a = (a -> Type0) -> Type0

let monotonic (w:w0 'a) =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> w p1 ==> w p2

val w (a : Type u#a) : Type u#(max 1 a)
let w a = pure_wp a

val w_ord (#a : Type) : w a -> w a -> Type0
let w_ord wp1 wp2 = forall p. wp1 p ==> wp2 p

unfold
val w_return (#a : Type) : a -> w a
unfold
let w_return x = as_pure_wp (fun p -> p x)

unfold
val w_bind (#a #b : Type) : w a -> (a -> w b) -> w b
unfold
let w_bind wp1 k =
  elim_pure_wp_monotonicity_forall ();
  as_pure_wp (fun p -> wp1 (fun x -> k x p))

val interp (#a : Type) : m a -> w a
let interp #a (l:a) = as_pure_wp (fun p -> p l)

let dm (a : Type) (wp : w a) : Type =
  p:(a -> Type0) -> squash (wp p) -> l:(m a){p l}

let irepr (a : Type) (wp: w a) = dm a wp

let ireturn (a : Type) (x : a) : irepr a (w_return x) = fun _ _ -> x

let ibind (a : Type) (b : Type) (wp_v : w a) (wp_f: a -> w b) (v : irepr a wp_v) (f : (x:a -> irepr b (wp_f x))) : irepr b (w_bind wp_v wp_f) =
  fun p _ -> f (v (fun x -> wp_f x p) ()) p ()

let isubcomp (a:Type) (wp1 wp2: w a) (f : irepr a wp1) : Pure (irepr a wp2) (requires w_ord wp2 wp1) (ensures fun _ -> True) = f

let wp_if_then_else (#a:Type) (wp1 wp2:w a) (b:bool) : w a=
  elim_pure_wp_monotonicity_forall ();
  as_pure_wp (fun p -> (b ==> wp1 p) /\ ((~b) ==> wp2 p))

let i_if_then_else (a : Type) (wp1 wp2 : w a) (f : irepr a wp1) (g : irepr a wp2) (b : bool) : Type =
  irepr a (wp_if_then_else wp1 wp2 b)

total
reifiable
reflectable
layered_effect {
  ND : a:Type -> wp : w a -> Effect
  with repr         = irepr;
       return       = ireturn;
       bind         = ibind;
       subcomp      = isubcomp;
       if_then_else = i_if_then_else
}

let lift_pure_nd (a:Type) (wp:pure_wp a) (f:(eqtype_as_type unit -> PURE a wp)) :
  Pure (irepr a wp) (requires True)
                    (ensures (fun _ -> True))
  = fun p _ -> elim_pure f p

sub_effect PURE ~> ND = lift_pure_nd

type box a = | Box of a

let g (x:int) : box int = Box x

let rewrite_inside_reify (f : int -> ND unit (as_pure_wp(fun p -> True))) (x' : int) : Tot unit =
  let _ = f in
  match g x' with
  | Box x ->
     let ll = reify (f x) (fun _ -> True) in
     assert (ll == ll) by begin
       let beq = T.nth_binder 3 in
       T.rewrite beq;
       ()
     end

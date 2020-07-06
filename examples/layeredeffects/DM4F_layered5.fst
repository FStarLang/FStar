module DM4F_layered5

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

(* Same as DM4F, but layered over a layered PURE without monotonicity *)
open ID5
open FStar.Tactics

(* Simulating state effect in DM4F, hopefully doable by a tactic. *)

type post_t st a =
  a -> st -> Type0

type wp (st:Type u#0) (a:Type u#ua) : Type u#(max 1 ua) =
  st -> post_t st a -> Type0

type repr (a:Type u#ua) (st:Type0) (wp : wp u#ua st a) : Type u#(max 1 ua) =
  s0:st -> ID (a & st) (fun p -> wp s0 (curry p))

unfold
let return_wp (#a:Type) (#st:Type0) (x:a) : wp st a =
  fun s0 p -> p x s0

let return (a:Type) (x:a) (st:Type0) : repr a st (return_wp x) =
  fun s0 -> (x, s0)

unfold
let bind_wp (#a:Type) (#b:Type) (#st:Type0)
  (w1 : wp st a) (w2 : a -> wp st b) : wp st b =
  fun s0 p -> w1 s0 (fun y s1 -> squash (w2 y s1 p))
  // this squash is so bind works, because for some reason an
  // auto_squash pops up. Perhaps an alternative is to work
  // on the repr of ID

let bind (a:Type) (b:Type) (st:Type0)
  (wp_c : wp st a)
  (wp_f : a -> wp st b)
  (c : repr a st wp_c)
  (f : (x:a -> repr b st (wp_f x)))
: repr b st (bind_wp wp_c wp_f)
   by (explode ();
       compute ();
       let b = nth_binder (-1) in
       squash_intro ();
       exact b)
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

let lift_id_st_wp #a #st (w : ID5.wp a) : wp st a =
  fun s0 p -> w (fun x -> p x s0)

(* It's odd that I *have* to use the repr here, instead of a thunked
ID a wp as above. *)
let lift_id_st a st wp (f : ID5.repr a wp)
  : repr a st (lift_id_st_wp wp)
  = fun s0 -> ID5.ID?.reflect (ID5.bind _ _ _ _ f (fun x -> ID5.return _ (x, s0)))

sub_effect ID ~> ST = lift_id_st

let null #st #a : wp st a =
  fun s0 p -> forall x s1. p x s1

let get #st () : ST st st (fun s0 p -> p s0 s0) =
  ST?.reflect (fun s0 -> (s0, s0))

let put #st (s:st) : ST unit st (fun _ p -> p () s) =
  ST?.reflect (fun _ -> ((), s))

[@@expect_failure [19]] // monotonicity?
let test () : ST int int null =
  let x = get () in
  put (x + x);
  get () + get ()

module DM4F_layered5

(* Same as DM4F, but layered over a layered PURE without monotonicity *)
open ID5
open FStar.Tactics
open Common

unfold
let pure_bind_wp (#a #b : Type) (w1 : ID5.wp a) (w2 : a -> ID5.wp b) : ID5.wp b =
  ID5.bind_wp w1 w2

(* Simulating state effect in DM4F, hopefully doable by a tactic. *)

type post_t st a =
  a -> st -> Type0

type wp (st:Type u#0) (a:Type u#ua) : Type u#(max 1 ua) =
  st -> post_t st a -> Type0
  
let iso1 #a #s (w : wp s a) : s -> (a & s -> Type0) -> Type0 =
  fun s p -> w s (curry p)
  
let iso2 #a #s (w : s -> (a & s -> Type0) -> Type0) : wp s a=
  fun s p -> w s (uncurry p)

type repr (a:Type u#ua) (st:Type0) (wp : wp u#ua st a) : Type u#(max 1 ua) =
  s0:st -> ID (a & st) (fun p -> wp s0 (curry p))

unfold
let return_wp (#a:Type) (#st:Type0) (x:a) : wp st a =
  fun s0 p -> p x s0
  //iso2 (fun s0 -> ID5.return_wp (x, s0))
     // ^ reusing pure return

let return (a:Type) (x:a) (st:Type0) : repr a st (return_wp x) =
  fun s0 -> (x, s0)

unfold
let bind_wp (#a:Type) (#b:Type) (#st:Type0)
  (w1 : wp st a) (w2 : a -> wp st b) : wp st b =
  fun s0 p -> w1 s0 (fun y s1 -> w2 y s1 p)
  //iso2 (fun s0 -> pure_bind_wp (iso1 w1 s0) (fun (y, s1) -> iso1 (w2 y) s1))
    // ^ reusing pure bind

[@@ resolve_implicits; refine]
let resolve_tac () : Tac unit =
  compute ();
  explode ();
  ()
  
let bind (a:Type) (b:Type) (st:Type0)
  (wp_c : wp st a)
  (wp_f : a -> wp st b)
  (c : repr a st wp_c)
  (f : (x:a -> repr b st (wp_f x)))
: repr b st (bind_wp wp_c wp_f)
= fun s0 ->
      //let (y, s1) = c s0 in
      //f y s1
      // GM: argh! using the match above introduces noise in the VC, a true precondition
      // that becomes a pain since we don't have monotonicity nor even extensionality
      let r = c s0 in
      f (fst r) (snd r)

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
  (#[@@refine] u : squash (stronger wpg wpf))
  (f : repr a st wpf)
  : repr a st wpg
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

// this now works!!!
let test () : ST int int null =
  let x = get () in
  put (x + x);
  get () + get ()

let addx (x:int) : ST unit int (fun s0 p -> p () (s0+x)) =
  let y = get () in
  put (x+y)

let add_via_state (x y : int) : ST int int (fun s0 p -> p (x+y) s0) =
  let o = get () in
  put x;
  addx y;
  let r = get () in
  put o;
  r

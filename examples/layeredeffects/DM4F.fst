module DM4F

open FStar.Monotonic.Pure

#set-options "--print_universes"

(* Simulating state effect in DM4F, hopefully doable by a tactic. *)

type wp0 (st:Type u#0) (a:Type u#ua) : Type u#(max 1 ua) =
  st -> (a & st -> Type0) -> Type0

let st_monotonic #st #a (w : wp0 st a) : Type0 =
  //forall s0 p1 p2. (forall r. p1 r ==> p2 r) ==> w s0 p1 ==> w s0 p2
  // ^ this version seems to be less SMT-friendly
  forall s0 p1 p2. (forall x s1. p1 (x, s1) ==> p2 (x, s1)) ==> w s0 p1 ==> w s0 p2

type wp st a = w:(wp0 st a){st_monotonic w}

type repr (a:Type u#ua) (st:Type0) (wp : wp u#ua st a) : Type u#ua =
  s0:st -> PURE (a & st) (as_pure_wp (wp s0))

unfold
let return_wp (#a:Type) (#st:Type0) (x:a) : wp st a = fun s0 p -> p (x, s0)

let return (a:Type) (x:a) (st:Type0) : repr a st (return_wp x) =
  fun s0 -> (x, s0)

unfold
let bind_wp (#a #b:Type) (#st:Type0) (wp_c:wp st a) (wp_f:a -> wp st b) : wp st b =
  fun s0 p -> wp_c s0 (fun (y, s1) -> wp_f y s1 p)

let bind (a:Type) (b:Type) (st:Type0)
  (wp_c : wp st a)
  (wp_f : a -> wp st b)
  (c : repr a st wp_c)
  (f : (x:a -> repr b st (wp_f x)))
: repr b st  (bind_wp wp_c wp_f)
= fun s0 -> let (y, s1) = c s0 in
         f y s1

unfold
let ite_wp (#a:Type) (#st:Type0) (wpf wpg:wp st a) (b:bool) : wp st a =
  fun s0 p -> (b ==> wpf s0 p) /\ ((~b) ==> wpg s0 p)

let if_then_else
  (a:Type)
  (st:Type0)
  (wpf wpg : wp st a)
  (f : repr a st wpf)
  (g : repr a st wpg)
  (b : bool)
  : Type
  = repr a st (ite_wp wpf wpg b)

unfold
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
effect {
  ST (a:Type) ([@@@ effect_param] st:Type0) (_:wp st a)
  with {repr; return; bind; if_then_else; subcomp}
}

unfold
let lift_wp (#a:Type) (#st:Type0) (w:pure_wp a) : wp st a =
  elim_pure_wp_monotonicity_forall ();
  fun s0 p -> w (fun x -> p (x, s0))

let lift_pure_st a wp st (f : unit -> PURE a wp)
  : repr a st (lift_wp wp)
  = elim_pure_wp_monotonicity_forall ();
    fun s0 -> (f (), s0)

sub_effect PURE ~> ST = lift_pure_st

let null #st #a : wp st a =
  fun s0 p -> forall r. p r

let get #st () : ST st st (fun s0 p -> p (s0, s0)) =
  ST?.reflect (fun s0 -> (s0, s0))

let put #st (s:st) : ST unit st (fun _ p -> p ((), s)) =
  ST?.reflect (fun _ -> ((), s))

let test () : ST int int null =
  let x = get () in
  put (x + x);
  get () + get ()

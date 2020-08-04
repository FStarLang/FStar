module Steel.Stepper

open FStar.PCM

let even = n:nat{n % 2 == 0}
let odd = n:nat{n % 2 <> 0}

let abs (n:int) : nat = if n >= 0 then n else -n
let max (n m:nat) : nat = if n >= m then n else m


noeq
type stepper =
  | V : n:nat{n > 0} -> stepper // the real value " whole value "
  | Even : n:nat -> stepper
  | Odd  : n:nat -> stepper
  | None : stepper

let composable' (s0 s1:stepper) : prop =
    match s0, s1 with
    | _, None
    | None, _ -> True
    | Even n, Odd m
    | Odd m , Even n -> n % 2 == 0 /\ m % 2 <> 0 /\ abs (m-n) == 1
    | _ -> False

let composable : symrel stepper = composable'

let compose (s0:stepper) (s1:stepper{composable s0 s1}) =
    match s0, s1 with
    | a, None
    | None, a -> a
    | Even n, Odd m
    | Odd m, Even n -> V (max n m)

let p' : pcm' stepper = { composable = composable; op = compose; one = None }

let lemma_comm (x:stepper) (y:stepper{composable x y}) :
  Lemma (compose x y == compose y x)
  = ()

let lemma_assoc_l (x y:stepper) (z:stepper{composable y z /\ composable x (compose y z)})
  : Lemma (composable x y /\ composable (compose x y) z /\
           compose x (compose y z) == compose (compose x y) z)
  = ()

let lemma_assoc_r (x y:stepper) (z:stepper{composable x y /\ composable (compose x y) z})
  : Lemma (composable y z /\ composable x (compose y z) /\
           compose x (compose y z) == compose (compose x y) z)
  = ()

let lemma_is_unit (x:stepper) : Lemma (composable x None /\ compose x None == x)
  = ()

let p : pcm stepper =
  { p = p';
    comm = lemma_comm;
    assoc = lemma_assoc_l;
    assoc_r = lemma_assoc_r;
    is_unit = lemma_is_unit}


open Steel.Memory
open Steel.FramingEffect
open FStar.Ghost

assume val pts_to (r:ref stepper p) (v:erased stepper) : slprop u#1

let v (r:ref stepper p) (n:nat{n > 0}) : slprop = pts_to r (V n)
let s_even (r:ref stepper p) (n:nat) : slprop  = pts_to r (Even n)
let s_odd (r:ref stepper p) (n:nat) : slprop  = pts_to r (Odd n)

// TODO: Postcondition should be pts_to r v0
// Should be done in conjunction with "fictional" SL to upd with only Even/Odd
assume
val get (r:ref stepper p) (v0:erased stepper)
  : SteelT (v:stepper{compatible p v0 v}) (pts_to r v0) (fun v -> pts_to r v)

assume
val upd (r:ref stepper p) (v0:erased stepper) (v1:stepper { frame_preserving p v0 v1})
  : SteelT unit (pts_to r v0) (fun _ -> pts_to r v1)

assume
val alloc (x:stepper{compatible p x x})
  : SteelT (ref stepper p) emp (fun r -> pts_to r x)

assume
val split (r:ref stepper p) (v_full v0 v1:stepper) (_:squash (composable v0 v1)) (_:squash (v_full == compose v0 v1))
  : SteelT unit (pts_to r v_full) (fun _ -> pts_to r v0 `star` pts_to r v1)

assume val h_admit (#a:Type) (p:slprop) (q:a -> slprop) : SteelT a p (fun x -> q x)

assume
val cond (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop) (pre:bool -> prop)
         (then_: (unit -> Steel a (p true) (q true) (fun h -> pre true) (fun _ _ _ -> True)))
         (else_: (unit -> Steel a (p false) (q false) (fun h -> pre false) (fun _ _ _ -> True)))
  : Steel a (p b) (q b) (fun h ->  pre b) (fun _ _ _ -> True)

assume
val drop (p:slprop) : SteelT unit p (fun _ -> emp)

assume
val change_slprop
  (p q:slprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

val new_stepper (u:unit) : SteelT (ref stepper p) emp (fun r -> s_odd r 1 `star` s_even r 0)

let new_stepper _ =
  let r = alloc (V 1) in
  split r (V 1) (Odd 1) (Even 0) () ();
  r

val incr_even_write (r:ref stepper p) (x:stepper{V? x})
  : Steel nat (pts_to r x) (fun n -> s_even r n) (fun _ -> squash (V?.n x % 2 <> 0)) (fun _ _ _ -> True)

let incr_even_write r s =
  let (x:nat{x > 0}) = V?.n s in
  change_slprop (pts_to r s) (pts_to r (V x)) (fun _ -> ());

  let y':nat = x+1 in
  upd r (V x) (Even y');
  y'


val incr_even_noop (r:ref stepper p) (x:stepper{V? x})
  : Steel nat (pts_to r x) (fun x -> s_even r x) (fun _ -> squash (V?.n x % 2 = 0)) (fun _ _ _ -> True)

let incr_even_noop r s =
  let (x:nat{x > 0}) = V?.n s in
  change_slprop (pts_to r s) (pts_to r (V x)) (fun _ -> ());
  split r (V x) (Even x) (Odd (x-1)) () ();
  drop (s_odd r (x-1));
  x

val incr_even (r:ref stepper p) (n:nat) : SteelT nat (s_even r n) (fun n' -> s_even r n')

let incr_even r n =
  let x = get r (Even n) in
  assert (V? x \/ Even? x);
  // Assumes we get the "full heap" value
  // TODO: The PCM should be more complete to include "permissions"
  assume (V? x);
  let n' = V?.n x in
  cond (n = n') (fun b -> pts_to r x) (fun _ n' -> s_even r n')
    (fun b -> if b then n' % 2 == 0 else squash (n' % 2 <> 0))
    (fun _ -> incr_even_noop r x)
    (fun _ -> incr_even_write r x)

val incr_odd_noop (r:ref stepper p) (x:stepper{V? x})
  : Steel nat (pts_to r x) (fun n -> s_odd r n) (fun _ -> squash (V?.n x % 2 <> 0)) (fun _ _ _ -> True)

let incr_odd_noop r s =
  let (x:nat{x > 0}) = V?.n s in
  change_slprop (pts_to r s) (pts_to r (V x)) (fun _ -> ());
  split r (V x) (Even (x-1)) (Odd x) () ();
  drop (s_even r (x-1));
  x

val incr_odd_write (r:ref stepper p) (x:stepper{V? x})
  : Steel nat (pts_to r x) (fun x -> s_odd r x) (fun _ -> squash (V?.n x % 2 = 0)) (fun _ _ _ -> True)

let incr_odd_write r s =
  let (x:nat{x > 0}) = V?.n s in
  change_slprop (pts_to r s) (pts_to r (V x)) (fun _ -> ());

  let y':nat = x+1 in
  upd r (V x) (Odd y');
  y'

val incr_odd (r:ref stepper p) (n:nat) : SteelT nat (s_odd r n) (fun n' -> s_odd r n')

let incr_odd r n =
  let x = get r (Odd n) in
  assert (V? x \/ Odd? x);
  // Assumes we get the "full heap" value
  // TODO: The PCM should be more complete to include "permissions"
  assume (V? x);
  let n' = V?.n x in
  cond (n = n') (fun b -> pts_to r x) (fun _ n' -> s_odd r n')
    (fun b -> if b then squash (n' % 2 <> 0) else squash (n' % 2 = 0))
    (fun _ -> incr_odd_noop r x)
    (fun _ -> incr_odd_write r x)

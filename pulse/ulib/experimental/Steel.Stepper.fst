module Steel.Stepper

open FStar.PCM

let even = n:nat{n % 2 == 0}
let odd = n:nat{n % 2 <> 0}

let abs (n:int) : nat = if n >= 0 then n else -n
let max (n m:nat) : nat = if n >= m then n else m


noeq
type stepper =
  | V : n:nat{n > 0} -> stepper // the real value " whole value "
  | Even : n:even -> stepper
  | Odd  : n:odd -> stepper
  | EvenWriteable : even -> stepper
  | OddWriteable : odd -> stepper
  | None : stepper

let composable' (s0 s1:stepper) : prop =
    match s0, s1 with
    | _, None
    | None, _ -> True
    | Even n, Odd m
    | Odd m , Even n -> abs (m-n) == 1
    | EvenWriteable n, Odd m | Odd m, EvenWriteable n -> m - n == 1
    | OddWriteable n, Even m | Even m, OddWriteable n -> m - n == 1
    | _ -> False

let composable : symrel stepper = composable'

let compose (s0:stepper) (s1:stepper{composable s0 s1}) =
    match s0, s1 with
    | a, None
    | None, a -> a
    | Even n, Odd m
    | Odd m, Even n -> V (max n m)
    | Odd m, EvenWriteable n | EvenWriteable n, Odd m -> V m
    | Even m, OddWriteable n | OddWriteable n, Even m -> V m

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
let s_even (r:ref stepper p) (n:nat) : Pure slprop (n % 2 == 0) (fun _ -> True)  = pts_to r (Even n)
let s_odd (r:ref stepper p) (n:nat) : Pure slprop (n % 2 <> 0) (fun _ -> True)  = pts_to r (Odd n)

// Stateful version of actions
// get_even/get_odd/upd_even/upd_odd should be done in
// conjunction with "fictional" SL
assume
val get_even (r:ref stepper p) (n0:even)
  : SteelT (n:nat{n > 0 /\ compatible p (Even n0) (V n)}) (pts_to r (Even n0))
           (fun n -> if n = n0 then pts_to r (Even n0) else pts_to r (EvenWriteable n0))

assume
val get_odd (r:ref stepper p) (n0:odd)
  : SteelT (n:nat{n > 0 /\ compatible p (Odd n0) (V n)}) (pts_to r (Odd n0))
           (fun n -> if n = n0 then pts_to r (Odd n0) else pts_to r (OddWriteable n0))

assume
val upd_even (r:ref stepper p) (n:even) :
  SteelT unit (pts_to r (EvenWriteable n)) (fun _ -> pts_to r (Even (n+2)))

assume
val upd_odd (r:ref stepper p) (n:odd) :
  SteelT unit (pts_to r (OddWriteable n)) (fun _ -> pts_to r (Odd (n+2)))

assume
val alloc (x:stepper{compatible p x x})
  : SteelT (ref stepper p) emp (fun r -> pts_to r x)

assume
val split (r:ref stepper p) (v_full v0 v1:stepper)  : Steel unit (pts_to r v_full) (fun _ -> pts_to r v0 `star` pts_to r v1)
      (fun _ -> composable v0 v1 /\ v_full == compose v0 v1)
      (fun _ _ _ -> True)

// Assumed from basics

assume val h_admit (#a:Type) (p:slprop) (q:a -> slprop) : SteelT a p (fun x -> q x)

assume
val cond (#a:Type) (b:bool) (p: bool -> slprop) (q: bool -> a -> slprop)
         (then_: (unit -> SteelT a (p true) (q true)))
         (else_: (unit -> SteelT a (p false) (q false)))
  : SteelT a (p b) (q b)

assume
val drop (p:slprop) : SteelT unit p (fun _ -> emp)

assume
val change_slprop
  (p q:slprop)
  (proof: (m:mem) -> Lemma (requires interp p m) (ensures interp q m))
  : SteelT unit p (fun _ -> q)

// Core functions of stepper

val new_stepper (u:unit) : SteelT (ref stepper p) emp (fun r -> s_odd r 1 `star` s_even r 0)

let new_stepper _ =
  let r = alloc (V 1) in
  split r (V 1) (Odd 1) (Even 0);
  r

val incr_even (r:ref stepper p) (n:even) : SteelT unit (s_even r n) (fun _ -> s_even r (n + 2))

let rec incr_even r n =
  let x = get_even r n in
  cond (x = n)
    (fun b -> if b then pts_to r (Even n) else pts_to r (EvenWriteable n)) (fun _ _ -> s_even r (n+2))
    (fun _ -> incr_even r n)
    (fun _ -> upd_even r n)

val incr_odd (r:ref stepper p) (n:odd) : SteelT unit (s_odd r n) (fun _ -> s_odd r (n + 2))

let rec incr_odd r n =
  let x = get_odd r n in
  cond (x = n)
    (fun b -> if b then pts_to r (Odd n) else pts_to r (OddWriteable n)) (fun _ _ -> s_odd r (n+2))
    (fun _ -> incr_odd r n)
    (fun _ -> upd_odd r n)


// Main driver incrementing the stepper forever in parallel

// Par is assumed from basics

assume
val par (#preL:slprop) (#postL:unit -> slprop)
        (f:unit -> SteelT unit preL postL)
        (#preR:slprop) (#postR:unit -> slprop)
        (g:unit -> SteelT unit preR postR)
  : SteelT unit
    (preL `star` preR)
    (fun x -> postL () `star` postR ())

val rec_incr_even (r:ref stepper p) (n:even)
  : SteelT unit (s_even r n) (fun _ -> emp)

let rec rec_incr_even r n =
  incr_even r n;
  rec_incr_even r (n+2)

val rec_incr_odd (r:ref stepper p) (n:odd)
  : SteelT unit (s_odd r n) (fun _ -> emp)

let rec rec_incr_odd r n =
  incr_odd r n;
  rec_incr_odd r (n+2)

val main (_:unit) : SteelT unit emp (fun _ -> emp)

let main () =
  let r = new_stepper () in
  par (fun _ -> rec_incr_even r 0) (fun _ -> rec_incr_odd r 1)

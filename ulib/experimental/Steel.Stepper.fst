module Steel.Stepper

open FStar.PCM

let even = n:nat{n % 2 == 0}
let odd = n:nat{n % 2 <> 0}

let abs (n:int) : nat = if n >= 0 then n else -n
let max (n m:nat) : nat = if n >= m then n else m


noeq
type stepper : Type u#1 =
  | V : n:nat{n > 0} -> stepper // the real value " whole value "
  | Even : n:even -> stepper
  | Odd  : n:odd -> stepper
  | EvenWriteable : even -> stepper
  | OddWriteable : odd -> stepper
  | None : stepper

let refine (s:stepper) : Tot prop = V? s \/ None? s

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
    is_unit = lemma_is_unit;
    refine = refine }

open Steel.Memory
open Steel.Effect
open FStar.Ghost

// Use erased values here to avoid some rewritings
val pts_to (r:ref stepper p) (v:erased stepper) : slprop u#1
let pts_to r v = pts_to r v

let v (r:ref stepper p) (n:nat{n > 0}) : slprop = pts_to r (V n)
let s_even (r:ref stepper p) (n:nat) : Pure slprop (n % 2 == 0) (fun _ -> True)  = pts_to r (Even n)
let s_odd (r:ref stepper p) (n:nat) : Pure slprop (n % 2 <> 0) (fun _ -> True)  = pts_to r (Odd n)



let frame_compatible (x:erased stepper) (v y:stepper) =
  (forall (frame:stepper). {:pattern (composable x frame)}
            composable x frame /\
            v == compose x frame ==>
            composable y frame /\
            v == compose y frame)

let select_refine' (r:ref stepper p)
                  (x:erased stepper)
                  (f:(v:stepper{compatible p x v}
                      -> GTot (y:stepper{compatible p y v /\
                                  frame_compatible x v y})))
   : SteelT  (v:stepper{compatible p x v /\ refine v})
             (Memory.pts_to r x)
             (fun v -> Memory.pts_to r (f v))
   = select_refine r x f

let select_refine (r:ref stepper p)
                  (x:erased stepper)
                  (f:(v:stepper{compatible p x v}
                      -> GTot (y:stepper{compatible p y v /\
                                  frame_compatible x v y})))
   : SteelT  (v:stepper{compatible p x v /\ refine v})
             (pts_to r x)
             (fun v -> pts_to r (f v))
   = let v = select_refine' r x f in
     change_slprop (Memory.pts_to r (f v)) (pts_to r (f v)) (fun _ -> ());
     v


(** Updating a ref cell for a user-defined PCM *)

val upd_gen_action (r:ref stepper p)
                   (x y:Ghost.erased stepper)
                   (f:FStar.PCM.frame_preserving_upd p x y)
  : SteelT unit (pts_to r x) (fun _ -> pts_to r y)

let upd_gen_action r x y f = upd_gen r x y f

let f_even (n0:even) (v:stepper{compatible p (Even n0) v})
  : GTot (y:stepper{compatible p y v /\ frame_compatible (Even n0) v y})
  = match v with
    | Even n0 -> Even n0
    | EvenWriteable n0 -> EvenWriteable n0
    | V n -> if n = n0 then Even n0 else EvenWriteable n0

let f_odd (n0:odd) (v:stepper{compatible p (Odd n0) v})
  : GTot (y:stepper{compatible p y v /\ frame_compatible (Odd n0) v y})
  = match v with
    | Odd n0 -> Odd n0
    | OddWriteable n0 -> OddWriteable n0
    | V n -> if n = n0 then Odd n0 else OddWriteable n0


// Stateful version of actions
// get_even/get_odd/upd_even/upd_odd should be done in
// conjunction with "fictional" SL
let get_even (r:ref stepper p) (n0:even)
  : Steel nat
          (pts_to r (Even n0))
          (fun n -> pts_to r (if n = n0 then Even n0 else EvenWriteable n0))
          (requires fun _ -> True)
          (ensures fun _ n _ -> n > 0 /\ compatible p (Even n0) (V n))
  = let v = select_refine r (Even n0) (f_even n0) in
    let n:nat = V?.n v in
    change_slprop (pts_to r (f_even n0 v)) (pts_to r (if n = n0 then Even n0 else EvenWriteable n0)) (fun _ -> ());
    n

let get_odd (r:ref stepper p) (n0:odd)
  : Steel nat
          (pts_to r (Odd n0))
          (fun n -> pts_to r (if n = n0 then Odd n0 else OddWriteable n0))
          (requires fun _ -> True)
          (ensures fun _ n _ -> n > 0 /\ compatible p (Odd n0) (V n))
  = let v = select_refine r (Odd n0) (f_odd n0) in
    let n:nat = V?.n v in
    change_slprop (pts_to r (f_odd n0 v)) (pts_to r (if n = n0 then Odd n0 else OddWriteable n0)) (fun _ -> ());
    n

let upd_even_f (n:even) : FStar.PCM.frame_preserving_upd p
                            (EvenWriteable n)
                            (Even (n + 2))
  = let f
      : FStar.PCM.frame_preserving_upd_0 p (EvenWriteable n) (Even (n + 2))
      = function
        | EvenWriteable n -> Even (n + 2)
        | V n -> V (n + 1)
    in
    f

let upd_odd_f (n:odd) : FStar.PCM.frame_preserving_upd p (OddWriteable n) (Odd (n + 2))
  = let f
      : FStar.PCM.frame_preserving_upd_0 p (OddWriteable n) (Odd (n + 2))
      = function
        | OddWriteable n -> Odd (n + 2)
        | V n -> V (n + 1)
    in
    f

let upd_even (r:ref stepper p) (n:even)
  : SteelT unit (pts_to r (EvenWriteable n)) (fun _ -> pts_to r (Even (n+2)))
  = upd_gen_action r (Ghost.hide (EvenWriteable n))
                     (Ghost.hide (Even (n + 2)))
                     (upd_even_f n)

let upd_odd (r:ref stepper p) (n:odd)
  : SteelT unit (pts_to r (OddWriteable n)) (fun _ -> pts_to r (Odd (n+2)))
  = upd_gen_action r (Ghost.hide (OddWriteable n))
                     (Ghost.hide (Odd (n + 2)))
                     (upd_odd_f n)

val alloc (x:stepper{compatible p x x /\ refine x})
  : SteelT (ref stepper p) emp (fun r -> pts_to r x)

let alloc x =
  let r = alloc x in
  change_slprop (Memory.pts_to r x) (pts_to r x) (fun _ -> ());
  r

val split (r:ref stepper p) (v_full v0 v1:stepper)
  : Steel unit (pts_to r v_full) (fun _ -> pts_to r v0 `star` pts_to r v1)
      (fun _ -> composable v0 v1 /\ v_full == compose v0 v1)
      (fun _ _ _ -> True)

let split r v_full v0 v1 = split r v_full v0 v1

// Core functions of stepper

val new_stepper (u:unit) : SteelT (ref stepper p) emp (fun r -> s_odd r 1 `star` s_even r 0)

let new_stepper _ =
  let r = alloc (V 1) in
  split r (V 1) (Odd 1) (Even 0);
  r

val incr_even (r:ref stepper p) (n:even) : SteelT unit (s_even r n) (fun _ -> s_even r (n + 2))

let rec incr_even r n =
  let x = get_even r n in
  if x = n then (
    change_slprop
      (pts_to r (if x = n then Even n else EvenWriteable n))
      (s_even r n) (fun _ -> ());
    incr_even r n) else
    (change_slprop
      (pts_to r (if x = n then Even n else EvenWriteable n))
      (pts_to r (EvenWriteable n)) (fun _ -> ());
    upd_even r n)

val incr_odd (r:ref stepper p) (n:odd) : SteelT unit (s_odd r n) (fun _ -> s_odd r (n + 2))

let rec incr_odd r n =
  let x = get_odd r n in
  if x = n then (
    change_slprop
      (pts_to r (if x = n then Odd n else OddWriteable n))
      (s_odd r n) (fun _ -> ());
    incr_odd r n) else
    (change_slprop
      (pts_to r (if x = n then Odd n else OddWriteable n))
      (pts_to r (OddWriteable n)) (fun _ -> ());
    upd_odd r n)

// Main driver incrementing the stepper forever in parallel

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
  let _ = par (fun _ -> rec_incr_even r 0) (fun _ -> rec_incr_odd r 1) in
  ()

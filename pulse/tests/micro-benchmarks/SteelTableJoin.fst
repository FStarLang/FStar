module SteelTableJoin
open Steel.ST.GenElim

assume
val ptr : Type0

assume
val pts_to1 (p: ptr) (v: Ghost.erased nat) : vprop

assume
val split
  (#v: Ghost.erased nat)
  (p: ptr)
: STT ptr
    (pts_to1 p v)
    (fun res -> exists_ (fun vl -> exists_ (fun vr -> pts_to1 p vl `star` pts_to1 res vr)))


assume val join (#opened: _) (#pl #pr: Ghost.erased nat) (al ar: ptr) : STGhostT (Ghost.erased nat) opened (pts_to1 al pl `star` pts_to1 ar pr) (fun res -> pts_to1 al res)

assume val v1 (#p: Ghost.erased nat) (a: ptr) (err: ptr) : STT unit
  (pts_to1 a p `star` pts_to1 err 0)
  (fun _ -> pts_to1 a p `star` exists_ (fun v -> pts_to1 err v))

let v2 (#p: Ghost.erased nat) (al: ptr) (err: ptr) : STT unit
  (pts_to1 al p `star` pts_to1 err 0)
  (fun _ -> exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)))
= let ar = split al in
  let _ = gen_elim () in
  let _ = v1 ar err in
  let _ = gen_elim () in
  let _ = join al ar in
  intro_exists _ (fun v ->  pts_to1 al _ `star` pts_to1 err v);
  intro_exists _ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v));
  return ()

let v2' (#p: Ghost.erased nat) (al: ptr) (err: ptr) : STT unit
  (pts_to1 al p `star` pts_to1 err 0)
  (fun _ -> exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)))
= let ar = split al in
  let _ = gen_elim () in
  let _ = v1 ar err in
  let _ = elim_exists () in
//  let _ = elim_pure _ in
  let _ = noop () in
  let _ = join al ar in
  return ()

#set-options "--print_implicits"

assume val noop_f (#opened: _) (#p: vprop) (_: unit) : STGhostF unit opened p (fun _ -> p) True (fun _ -> True)

#set-options "--print_full_names"


let v3 (#pl #pr: Ghost.erased nat) (al: ptr) (ar: ptr) (err: ptr) : STT unit
  (pts_to1 al pl `star` pts_to1 ar pr `star` exists_ (fun v -> pts_to1 err v))
  (fun _ -> exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)))
= let _ = gen_elim () in
  let _ = join al ar in
//  let _ = gen_elim () in
//  assert_ (exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)));
  noop ()


let v3' (#p: Ghost.erased nat) (al: ptr) (err: ptr) : STT unit
  (pts_to1 al p `star` pts_to1 err 0)
  (fun _ -> exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)))
= let ar = split al in
  let _ = gen_elim () in
  let _ = v1 ar err in
  let _ = gen_elim () in
  let _ = join al ar in
  noop ()

//  let _ = gen_elim () in
//  assert_ (exists_ (fun p -> exists_ (fun v -> pts_to1 al p `star` pts_to1 err v)));


(*
[@__reduce__]
let f0: vprop = ... 

let f = f0

rewrite f0 f
rewrite f f0


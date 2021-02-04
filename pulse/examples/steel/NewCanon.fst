module NewCanon

open Steel.Memory
open Steel.Effect

assume val p (#n:int) (n2:int) : slprop
assume val q (#n:int) (#n':int) (n2:int) : slprop

assume val palloc (#n:int) (n2:int) : SteelT unit emp (fun _ -> p #n n2)
assume val pwrite (#n:int) (#oldn:int) (newn:int) : SteelT unit (p #n oldn) (fun _ -> p #n newn)

assume val ref : Type0
assume val ptr (_:ref) : slprop u#1

assume val alloc (x:int)  : SteelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

let test_imp (x:int) : SteelT unit emp (fun _ -> p #1 1)  =
  let _ = palloc 0 in
  pwrite 1

let test1 (x:int) : SteelT ref emp ptr =
  let y = alloc x in y

let test2 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  x

let test3 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)
  = let x = read r in
    let y = read r in
    x

let test4 (r:ref) : SteelT ref (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc 0 in
    y

let test5 (r1 r2:ref) : SteelT ref (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc 0 in
    y

let test6 (r1 r2:ref) : SteelT unit (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = read r1 in
    ()

let test7 (a:unit) : SteelT ref emp (fun y -> ptr y) =
  let x = alloc 0 in
  let v = read x in
  x

let test8 (x:ref) : SteelT int (ptr x) (fun _ -> ptr x)
  = let v = read x in
    let y = alloc v in
    let v = read y in
    free y;
    // Can mix assertions
    assert (1 == 1);
    v

assume val noop (_:unit) : SteelT unit emp (fun _ -> emp)

let test_dep_frame () : SteelT ref emp (fun r -> ptr r)
  = let r = alloc 0 in
    noop ();
    r

open Steel.FractionalPermission
open FStar.Ghost
assume val reference (a:Type0) : Type0
assume val pts_to (#a:Type0) (r:reference a) (p:perm) (v:erased a) : slprop u#1
assume val rread (#a:Type) (#p:perm) (#v:erased a) (r:reference a) : SteelT (x:a{x == Ghost.reveal v}) (pts_to r p v) (fun _ -> pts_to r p v)
assume val rwrite (#a:Type) (#v:erased a) (r:reference a) (v':a) : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm (Ghost.hide v'))

assume val rwrite_alt (#a:Type) (#v:erased a) (r:reference a) (v'':erased a) (v':a{v'==Ghost.reveal v''})
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm v'')

assume val r : slprop

let read_write (#a:Type) (r0:reference a) (v0:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` r)
                (fun _ -> r `star` pts_to r0 full_perm v0)
  = let u0 = rread r0 in
    rwrite_alt r0 v0 u0


let swap (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread r0 in
    let u1 = rread r1 in
    rwrite_alt r0 v1 u1;
    rwrite_alt r1 v0 u0

assume
val rewrite_eq (#a:Type) (p:erased a -> slprop) (v0:erased a) (v1:erased a{v0 == v1})
  : SteelT unit (p v0) (fun _ -> p v1)

let swap2 (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread r0 in
    let u1 = rread r1 in
    rwrite r0 u1;
    rwrite r1 u0;
    rewrite_eq (pts_to r1 full_perm) (Ghost.hide u0) v0;
    rewrite_eq (pts_to r0 full_perm) (Ghost.hide u1) v1

open Steel.Effect.Atomic

assume val alloc2 (x:int)  : SteelAtomicT ref Set.empty observable emp (fun y -> ptr y)
assume val free2 (r:ref) : SteelAtomicT unit Set.empty observable (ptr r) (fun _ -> emp)
assume val ghost_read (r:ref) : SteelAtomicT int Set.empty unobservable (ptr r) (fun _ -> ptr r)

let test21 (x:int) : SteelAtomicT ref Set.empty observable emp ptr =
  let y = alloc2 x in y

[@expect_failure]
// Cannot have two observable atomic computations
let test22 (x:int) : SteelAtomicT unit Set.empty observable emp (fun _ -> emp) =
  let y = alloc2 x in
  free2 y

let test23 (r:ref) : SteelAtomicT int Set.empty unobservable (ptr r) (fun _ -> ptr r)
  = let x = ghost_read r in
    let y = ghost_read r in
    x

let test24 (r:ref) : SteelAtomicT ref Set.empty observable (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc2 0 in
    y

let test25 (r1 r2:ref) : SteelAtomicT ref Set.empty observable
    (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc2 0 in
    y

// Exercising subcomp on observability
let test26 (r1 r2:ref) : SteelAtomicT unit Set.empty observable (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = ghost_read r1 in
    ()

let test27 (a:unit) : SteelAtomicT ref Set.empty observable emp (fun y -> ptr y) =
  let x = alloc2 0 in
  let v = ghost_read x in
  x

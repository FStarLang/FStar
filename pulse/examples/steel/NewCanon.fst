module NewCanon

open FStar.Ghost
open Steel.FractionalPermission
open Steel.Memory
open Steel.SelEffect.Atomic
open Steel.SelEffect

assume val p (#n:int) (n2:int) : vprop
assume val q (#n:int) (#n':int) (n2:int) : vprop

assume val palloc (#n:int) (n2:int) : SteelSelT unit emp (fun _ -> p #n n2)
assume val pwrite (#n:int) (#oldn:int) (newn:int) : SteelSelT unit (p #n oldn) (fun _ -> p #n newn)

assume val ref : Type0
assume val ptr (_:ref) : vprop

assume val alloc (x:int)  : SteelSelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelSelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelSelT int (ptr r) (fun _ -> ptr r)

let test_imp (x:int) : SteelSelT unit emp (fun _ -> p #1 1)  =
  let _ = palloc 0 in
  pwrite 1

let test1 (x:int) : SteelSelT ref emp ptr =
  let y = alloc x in y

let test2 (r:ref) : SteelSelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  x

let test3 (r:ref) : SteelSelT int (ptr r) (fun _ -> ptr r)
  = let x = read r in
    let y = read r in
    x

let test4 (r:ref) : SteelSelT ref (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc 0 in
    y

let test5 (r1 r2:ref) : SteelSelT ref (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc 0 in
    y

let test6 (r1 r2:ref) : SteelSelT unit (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = read r1 in
    ()

let test7 (a:unit) : SteelSelT ref emp (fun y -> ptr y) =
  let x = alloc 0 in
  let v = read x in
  x

let test8 (x:ref) : SteelSelT int (ptr x) (fun _ -> ptr x)
  = let v = read x in
    let y = alloc v in
    let v = read y in
    free y;
    // Can mix assertions
    assert (1 == 1);
    v

let test_dep_frame () : SteelSelT ref emp (fun r -> ptr r)
  = let r = alloc 0 in
    noop ();
    return r

assume val reference (a:Type0) : Type0
assume val pts_to (#a:Type0) (r:reference a) (p:perm) (v:erased a) : vprop
assume val rread (#a:Type) (#p:perm) (#v:erased a) (r:reference a) : SteelSelT (x:a{x == Ghost.reveal v}) (pts_to r p v) (fun _ -> pts_to r p v)
assume val rwrite (#a:Type) (#v:erased a) (r:reference a) (v':a) : SteelSelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm (Ghost.hide v'))

assume val rwrite_alt (#a:Type) (#v:erased a) (r:reference a) (v'':erased a) (v':a{v'==Ghost.reveal v''})
  : SteelSelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm v'')

assume val r : vprop

let read_write (#a:Type) (r0:reference a) (v0:erased a)
  : SteelSelT unit (pts_to r0 full_perm v0 `star` r)
                (fun _ -> r `star` pts_to r0 full_perm v0)
  = let u0 = rread r0 in
    rwrite_alt r0 v0 u0


let swap (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelSelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread r0 in
    let u1 = rread r1 in
    rwrite_alt r0 v1 u1;
    rwrite_alt r1 v0 u0

assume
val rewrite_eq (#a:Type) (p:erased a -> vprop) (v0:erased a) (v1:erased a{v0 == v1})
  : SteelSelT unit (p v0) (fun _ -> p v1)

let swap2 (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelSelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread r0 in
    let u1 = rread r1 in
    rwrite r0 u1;
    rwrite r1 u0;
    rewrite_eq (pts_to r1 full_perm) (Ghost.hide u0) v0;
    rewrite_eq (pts_to r0 full_perm) (Ghost.hide u1) v1

assume val alloc2 (x:int)  : SteelSelAtomicT ref Set.empty emp (fun y -> ptr y)
assume val free2 (r:ref) : SteelSelAtomicT unit Set.empty (ptr r) (fun _ -> emp)
assume val ghost_read (r:ref) : SteelSelGhostT (erased int) Set.empty (ptr r) (fun _ -> ptr r)

let test21 (x:int) : SteelSelAtomicT ref Set.empty emp ptr =
  let y = alloc2 x in y

[@expect_failure]
// Cannot have two observable atomic computations
let test22 (x:int) : SteelSelAtomicT unit Set.empty emp (fun _ -> emp) =
  let y = alloc2 x in
  free2 y

let test23 (r:ref) : SteelSelGhostT (erased int) Set.empty (ptr r) (fun _ -> ptr r)
  = let x = ghost_read r in
    let y = ghost_read r in
    x

let test24 (r:ref) : SteelSelAtomicT ref Set.empty (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc2 0 in
    y

let test25 (r1 r2:ref) : SteelSelAtomicT ref Set.empty
    (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc2 0 in
    y

// Exercising subcomp on observability
let test26 (r1 r2:ref) : SteelSelAtomicT unit Set.empty (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = ghost_read r1 in
    ()

let test27 (a:unit) : SteelSelAtomicT ref Set.empty emp (fun y -> ptr y) =
  let x = alloc2 0 in
  let v = ghost_read x in
  return x

module FramingEffect.Tests

open Steel.Memory
open Steel.FramingEffect

assume val ref : Type0
assume val ptr (_:ref) : slprop u#1

assume val alloc (x:int)  : SteelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)

// [@expect_failure]
let test1 (x:int) : SteelT ref emp ptr =
  let y = alloc x in y

// #set-options "--debug Steel.Effects2.Tests --debug_level Extreme --debug_level Rel --debug_level LayeredEffectsEqns --print_implicits --ugly --debug_level TwoPhases --print_bound_var_types"
// [@expect_failure]
let test2 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r) =
  let x = read r in
  x

// [@expect_failure]
let test3 (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)
  = let x = read r in
    let y = read r in
    x

// [@expect_failure]
let test4 (r:ref) : SteelT ref (ptr r) (fun y -> ptr r `star` ptr y)
  = let y = alloc 0 in
    y

// [@expect_failure]
let test5 (r1 r2:ref) : SteelT ref (ptr r1 `star` ptr r2) (fun y -> ptr r1 `star` ptr r2 `star` ptr y)
  = let y = alloc 0 in
    y

// [@expect_failure]
let test6 (r1 r2:ref) : SteelT unit (ptr r1 `star` ptr r2) (fun _ -> ptr r2 `star` ptr r1)
  = let _ = read r1 in
    ()

// Scoping issue to debug
//[@expect_failure]
let test7 (a:unit) : SteelT ref emp (fun y -> ptr y) =
  let x = alloc 0 in
  let v = read x in
  x

(* scratch
Initial goals:
1: annot_sub_post, subcomp postresource between full computation and ptr
2: delay (can_be_split ..) subcomp preresource between emp and full computation

13: can_be_split_forall .., sl_implication in T-Bind_A_A when typechecking
    let v = read x in x

19: can_be_split_forall .., sl_implication in T-Bind_A_ when typechecking
    let x = alloc 0 in (let v = read x in x)

21: Equality binding the preresource from inferred computation in subcomp (?u1 = P in T-Let)
22: Equality binding the annotated preresource in subcomp (?u3 = E in T-Let)
23: Equality binding the annotated postresource in subcomp (?u4 = y.F in T-Let)
24: Equality binding the postresource from inferred computation in subcomp (?u2 = y.Q)
25. Equality binding the postresources when typechecking full computation (?u4 = z.Q in T-Bind_A_)
26. Equality binding the preresources when typechecking full computation (?u3 x = P in T-Bind_A_)
27. Equality binding the postresource of alloc when typechecking full computation (?u2 = y.F in T-Bind_A_)
28. Equality binding the preresource of alloc when typechecking full computation (?u1 = E in T-Bind_A_)
29. Equality binding postresource of return when typechecking let v = read x in x
(?u4 = z.F1 in T-Bind_A_A)
30. Equality binding preresource of return when typechecking let v = read x in x
(?u3 x = E1 in T-Bind_A_A)
31. Equality binding postresource of read when typechecking let v = read x in x
(?u2 = y.F in T-Bind_A_A)
32. Equality binding preresource of read when typechecking let v = read x in x
(?u1 = E in T-Bind_A_A)

uvars:
3: postresource of top-level annotation
4: preresource of top-level annotation
5: postresource of full computation
6: preresource of full computation
7: frame of read when typechecking let v = read x in x
8: postcondition of read when typechecking let v = read x in x
9: postcondition of alloc when typechecking let x = alloc 0 in (let v = read x in x)
10: postcondition of (let v = read x in x)
11: frame of alloc when typechecking let x = alloc 0 in (let v = read x in x)
12: precondition of alloc when typechecking let x = alloc 0 in (let..)
14: frame of (return) x when typechecking let v = read x in x
15: resource associated to (return) x
16: postresource of (return) x when typechecking let v = read x in x
17: preresource of (return) x when typechecking let v = read x in x
18: preresource of read when typechecking let v = read x in x
20: preresource of (let v = read x in x) when typechecking let x = alloc 0 in (let ..)
*)

let test8 (x:ref) : SteelT int (ptr x) (fun _ -> ptr x)
  = let v = read x in
    let y = alloc v in
    let v = read y in
    free y;
    // Can mix assertions
    assert (1 == 1);
    v

open Steel.FractionalPermission
open FStar.Ghost
assume val reference (a:Type0) : Type0
assume val pts_to (#a:Type0) (r:reference a) (p:perm) (v:erased a) : slprop u#1
assume val rread (#a:Type) (#p:perm) (#v:erased a) (r:reference a) : SteelT (x:a{x == Ghost.reveal v}) (pts_to r p v) (fun _ -> pts_to r p v)
assume val rwrite (#a:Type) (#v:erased a) (r:reference a) (v':a) : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm (Ghost.hide v'))

assume val rwrite_alt (#a:Type) (#v:erased a) (r:reference a) (v'':erased a) (v':a{v'==Ghost.reveal v''})
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm v'')

assume val p : slprop

// let test_steel_subcomp (#a:Type) (r0:reference a) (v0:erased a) (u0:a{u0 == Ghost.reveal v0})
//   : SteelT unit (pts_to r0 full_perm v0 `star` p)
//              (fun _ -> pts_to r0 full_perm v0 `star` p)
//   = rwrite_alt #_ #v0 r0 v0 u0

let read_write (#a:Type) (r0:reference a) (v0:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` p)
                (fun _ -> p `star` pts_to r0 full_perm v0)
  = let u0 = rread #_ #full_perm  #v0 r0 in
    rwrite_alt #_ #v0 r0 v0 u0


let swap (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread #_ #full_perm #v0 r0 in
    let u1 = rread #_ #full_perm #v1 r1 in
    rwrite_alt #_ #v0 r0 v1 u1;
    rwrite_alt #_ #v1 r1 v0 u0

assume
val rewrite_eq (#a:Type) (p:erased a -> slprop) (v0:erased a) (v1:erased a{v0 == v1})
  : SteelT unit (p v0) (fun _ -> p v1)

let swap2 (#a:Type) (r0 r1:reference a) (v0 v1:erased a)
  : SteelT unit (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
                (fun _ -> pts_to r0 full_perm v1 `star` pts_to r1 full_perm v0)
  = let u0 = rread #_ #full_perm #v0 r0 in
    let u1 = rread #_ #full_perm #v1 r1 in
    rwrite #_ #v0 r0 u1;
    rwrite #_ #v1 r1 u0;
    rewrite_eq (pts_to r1 full_perm) (Ghost.hide u0) v0;
    rewrite_eq (pts_to r0 full_perm) (Ghost.hide u1) v1

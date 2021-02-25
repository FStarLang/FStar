module Swap
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open FStar.Ghost
open Steel.Reference

(* Several variants *)

assume
val pts (#a:Type u#0) (r:ref a) (p:perm) (#[@@@ smt_fallback] v:erased a) : slprop u#1

assume
val p_read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : Steel a (pts r p #v) (fun x -> pts r p #x)
           (requires fun _ -> True)
           (ensures fun _ x _ -> x == Ghost.reveal v)

#set-options "--print_implicits"
// #set-options "--print_implicits --log_queries --tactic_trace_d 1"

let test (#v0 #v1:erased int) (r0 r1:ref int)
  : Steel unit
    (pts r0 full_perm #v0 `star` pts r1 full_perm #v1)
    (fun _ ->  pts r0 full_perm #0 `star`  pts r1 full_perm #v1)
    (requires fun h -> v0 == hide 0)
    (ensures fun _ _ _ -> True)
  = //let tmp0 = read r0 in
//    assume (v0 == hide 0);
//    let _:squash (v0 == hide 0) = admit() in
    let tmp1 = p_read r0 in
    let tmp2 = p_read r1 in
//    let tmp2 = read r1 in
//    assert (tmp1 == 0);
//    assert (v0 == hide 0);
    ()

(* Fails without an slprop rewriting, but prints 9 goals *)
[@expect_failure]
let swap (#a:_) (#v0 #v1:erased a) (r0 r1:ref a)
  : SteelT unit
    (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
    (fun _ ->  pts_to r0 full_perm v1 `star`  pts_to r1 full_perm v0)
  = let tmp0 = read r0 in
    let tmp1 = read r1 in
    write r0 tmp1;
    write r1 tmp0


// let swap0 (#a:_) (#v0 #v1:erased a) (r0 r1:ref a)
//   : SteelT unit
//     (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
//     (fun _ ->  pts_to r0 full_perm v1 `star`  pts_to r1 full_perm v0)
//   = let tmp0 = read r0 in
//     let tmp1 = read r1 in
//     write r0 tmp1;
//     write r1 tmp0;
//     change_slprop (pts_to r0 full_perm (Ghost.hide tmp1))
//                   (pts_to r0 full_perm v1)
//                   (fun _ -> ());
//     change_slprop (pts_to r1 full_perm (Ghost.hide tmp0))
//                   (pts_to r1 full_perm v0)
//                   (fun _ -> ())

let change_eq (#p:slprop)
              (#q:slprop)
  : Steel unit p (fun _ -> q) (fun _ -> p == q) (fun _ _ _ -> True)
  = change_slprop p q (fun _ -> ())

let swap1 (#a:Type0) (#v0 #v1:erased a) (r0 r1:ref a)
  : SteelT unit
    (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
    (fun _ ->  pts_to r0 full_perm v1 `star`  pts_to r1 full_perm v0)
  = let tmp0 = read r0 in
    let tmp1 = read r1 in
    write r0 tmp1;
    write r1 tmp0;
    change_eq
      #(pts_to r0 full_perm (Ghost.hide tmp1) `star`
        pts_to r1 full_perm (Ghost.hide tmp0))
      #(pts_to r0 full_perm v1 `star`
        pts_to r1 full_perm v0)

let change_eq' (#p:slprop)
               (#q:slprop)
               (_:unit)
  : Steel unit p (fun _ -> q)
    (requires fun _ -> p==q)
    (ensures fun _ _ _ -> True)
  = change_slprop p q (fun _ -> ())

[@expect_failure] //steelT </: steelF
let change_eqF (#p:slprop)
               (#q:slprop)
               (_:unit)
  : SteelF unit p (fun _ -> q)
    (requires fun _ -> p==q)
    (ensures fun _ _ _ -> True)
  = change_slprop p q (fun _ -> ())

let change_eqF (#p:slprop)
               (#q:slprop)
               (_:unit)
  : SteelF unit p (fun _ -> q)
    (requires fun _ -> p==q)
    (ensures fun _ _ _ -> True)
  = let _ = change_slprop p q (fun _ -> ()) in noop ()

[@expect_failure] //fails on a proof of (p==q) with a bad error location; not sure why it should be different than swap3. I had expected it to work better, actually
let swap4 (#a:_) (#v0 #v1:erased a) (r0 r1:ref a)
  : SteelT unit
    (pts_to r0 full_perm v0 `star` pts_to r1 full_perm v1)
    (fun _ ->  pts_to r0 full_perm v1 `star`  pts_to r1 full_perm v0)
  = let tmp0 = read r0 in
    let tmp1 = read r1 in
    write r0 tmp1;
    write r1 tmp0;
    change_eqF ()

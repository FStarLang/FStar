module Pulse.Lib.GhostReference
friend Pulse.Lib.Core
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost
module R = Steel.ST.GhostReference
module S = Steel.ST.Util
module T = FStar.Tactics
let ref = R.ref

[@@"__reduce__"; "__steel_reduce__"]
let pts_to = R.pts_to


let alloc' (#a:Type) (x:a)
  : stt_ghost (ref a) emp_inames S.emp (fun r -> R.pts_to r full_perm x)
  = fun _ -> 
     let r = R.alloc x in
     r
let alloc #a = alloc' #a

let read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost a emp_inames
        (R.pts_to r p n)
        (fun x -> R.pts_to r p x `S.star` S.pure (reveal n == x))
  = fun _ ->
        let v = R.read r in
         v
let ( ! ) #a = read #a

let ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
    = fun _ -> R.write r x

let free #a r #n = fun _ -> R.free r; ()

let share #a r #v #p
  = fun _ -> R.share r; ()

let gather' (#a:Type0) (r:R.ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (R.pts_to r p0 x0 `S.star` R.pts_to r p1 x1)
      (fun _ -> R.pts_to r (sum_perm p0 p1) x0 `S.star` S.pure (x0 == x1))
  = fun _ -> let _ = R.gather r in ()
let gather = gather'

let pts_to_injective_eq' (#a:Type0)
                         (#p #q:perm)
                         (#v0 #v1:a)
                         (r:R.ref a)
  : stt_ghost unit emp_inames
      (R.pts_to r p v0 `S.star` R.pts_to r q v1)
      (fun _ -> R.pts_to r p v0 `S.star` R.pts_to r q v0 `S.star` S.pure (v0 == v1))
    = fun _ -> let _ = R.pts_to_injective_eq #a #emp_inames #p #q #v0 #v1 r in ()
let pts_to_injective_eq = pts_to_injective_eq'
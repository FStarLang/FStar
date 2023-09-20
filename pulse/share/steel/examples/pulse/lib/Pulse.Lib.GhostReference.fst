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
let pts_to #a (r:ref a) (#[exact (`full_perm)] p:perm) (v:a) = R.pts_to r p v

let alloc' (#a:Type) (x:a)
  : stt_ghost (ref a) emp_inames S.emp (fun r -> R.pts_to r full_perm x)
  = fun _ -> 
     let r = R.alloc x in
     r
let alloc #a = alloc' #a

let read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost (erased a) emp_inames
        (R.pts_to r p n)
        (fun x -> R.pts_to r p x `S.star` S.pure (n == x))
  = fun _ ->
        let v = R.read r in
         v
let ( ! ) #a = read #a

let ( := ) (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
    = fun _ -> R.write r x; ()

let free #a r #n = fun _ -> R.free r; ()

let share #a #inames r #v #p
  = fun _ -> R.share r; ()

let gather' (#a:Type0) #inames (r:R.ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit inames
      (R.pts_to r p0 x0 `S.star` R.pts_to r p1 x1)
      (fun _ -> R.pts_to r (sum_perm p0 p1) x0 `S.star` S.pure (x0 == x1))
  = fun _ -> let _ = R.gather r in ()
let gather = gather'

let share2 (#a:Type) #inames (r:ref a) (#v:erased a)
  : stt_ghost unit inames
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)
  = share #a r #v

let gather2' (#a:Type) #inames (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r #(sum_perm one_half one_half) x0 ** pure (x0 == x1))
  = gather r

let gather2 (#a:Type) #inames (r:ref a) (#x0 #x1:erased a)
  : Tot (stt_ghost unit inames
           (pts_to r #one_half x0 ** pts_to r #one_half x1)
           (fun _ -> pts_to r #full_perm x0 ** pure (x0 == x1)))
=
  assert ((fun (_:unit) -> pts_to r #(sum_perm one_half one_half) x0 ** pure (x0 == x1))
       == (fun (_:unit) -> pts_to r #full_perm x0 ** pure (x0 == x1)))
      by (T.l_to_r [`double_one_half]);
  (* NB: I'm surprised this works without extensionality and a restricted_t... bug? *)
  coerce_eq () (gather2' #a #inames r #x0 #x1)

let pts_to_injective_eq (#a:Type0)
                         (#p #q:perm)
                         (#v0 #v1:a)
                         (r:R.ref a)
  : stt_ghost unit emp_inames
      (R.pts_to r p v0 `S.star` R.pts_to r q v1)
      (fun _ -> R.pts_to r p v0 `S.star` R.pts_to r q v0 `S.star` S.pure (v0 == v1))
    = fun _ -> let _ = R.pts_to_injective_eq #a #emp_inames #p #q #v0 #v1 r in ()

inline_for_extraction
let gref_non_informative (a:Type0) : non_informative_witness (ref a) =
  fun r -> reveal r

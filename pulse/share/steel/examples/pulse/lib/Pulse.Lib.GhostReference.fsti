module Pulse.Lib.GhostReference
open FStar.Tactics
open Pulse.Lib.Core
open Steel.FractionalPermission
open FStar.Ghost

[@@erasable]
val ref (a:Type u#0) : Type u#0

val pts_to (#a:Type) (r:ref a) (#[exact (`full_perm)]p:perm) (n:a) : vprop

val alloc (#a:Type) (x:a)
  : stt_ghost (ref a) emp_inames emp (fun r -> pts_to r x)
  
val ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost (erased a) emp_inames
        (pts_to r #p n)
        (fun x -> pts_to r #p x ** pure (n == x))

val ( := ) (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
  : stt_ghost unit emp_inames
        (pts_to r n) 
        (fun _ -> pts_to r x)

val free (#a:Type) (r:ref a) (#n:erased a)
  : stt_ghost unit emp_inames (pts_to r n) (fun _ -> emp)

val share (#a:Type) #inames (r:ref a) (#v:erased a) (#p:perm)
  : stt_ghost unit inames
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(half_perm p) v **
       pts_to r #(half_perm p) v)

val gather (#a:Type) #inames (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit inames
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(sum_perm p0 p1) x0 ** pure (x0 == x1))

(* Share/gather specialized to half permission *)
val share2 (#a:Type) #inames (r:ref a) (#v:erased a)
  : stt_ghost unit inames
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)

val gather2 (#a:Type) #inames (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun _ -> pts_to r x0 ** pure (x0 == x1))

val pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : stt_ghost unit emp_inames
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v0 ** pure (v0 == v1))

inline_for_extraction
val gref_non_informative (a:Type0) : non_informative_witness (ref a)

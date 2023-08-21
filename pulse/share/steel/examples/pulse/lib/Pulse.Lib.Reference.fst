module Pulse.Lib.Reference
friend Pulse.Lib.Core
open Steel.ST.Util
open Pulse.Lib.Core
module R = Steel.ST.Reference
module S = Steel.ST.Util
let ref = R.ref

[@@"__reduce__";"__steel_reduce__"]
let pts_to #a (r:ref a) (#[exact (`full_perm)] p:perm) (v:a) = R.pts_to r p v

let alloc #a x =
    fun _ -> 
        let r = R.alloc x in
        S.return r


let read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt a
        (R.pts_to r p n)
        (fun x -> R.pts_to r p x `star` S.pure (reveal n == x))
  = fun _ ->
        let v = R.read r in
        S.return v

module T = FStar.Tactics
let ( ! ) #a = read #a

let ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  : stt unit
        (pts_to r #full_perm n) 
        (fun _ -> pts_to r #full_perm (hide x))
   = fun _ ->
        R.write r x;
        S.return ()

let free #a (r:ref a) (#n:erased a)
    = fun _ ->
        R.free r;
        S.return ()

let share #a r #v #p
  = fun _ -> R.share r; ()

let gather (#a:Type) (r:R.ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (R.pts_to r p0 x0 `S.star` R.pts_to r p1 x1)
      (fun _ -> R.pts_to r (sum_perm p0 p1) x0 `S.star` S.pure (x0 == x1))
  = fun _ -> let _ = R.gather p1 r in ()

let share2 (#a:Type) (r:ref a) (#v:erased a)
  : stt_ghost unit emp_inames
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)
  = share #a r #v

let gather2' (#a:Type) (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit emp_inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r #(sum_perm one_half one_half) x0 `S.star` pure (x0 == x1))
  = gather r
let gather2 #a r #x0 #x1 =
  (* Need the coerce to change sum_perm one_half one_half into full_perm *)
  coerce_eq () (gather2' #a r #x0 #x1)

let read_atomic_alt (r:ref U32.t) (#n:erased U32.t) (#p:perm)
 : stt_atomic U32.t emp_inames
    (R.pts_to r p n)
    (fun x -> R.pts_to r p n `star` S.pure (reveal n == x))
  = fun _ ->
      let x = R.atomic_read_u32 r in
      S.intro_pure (reveal n == x);
      S.return x

let read_atomic = read_atomic_alt

let write_atomic (r:ref U32.t) (x:U32.t) (#n:erased U32.t)
  : stt_atomic unit emp_inames
    (R.pts_to r full_perm n)
    (fun _ -> R.pts_to r full_perm (hide x))
  = fun _ ->
      R.atomic_write_u32 r x;
      S.return ()

let with_local #a init #pre #ret_t #post body =
  fun _ -> 
    let body (r:R.ref a) 
      : STT ret_t
        (pre `star` R.pts_to r full_perm init)
        (fun v -> post v `star` exists_ (R.pts_to r full_perm))
      = S.rewrite
                (pre `star` R.pts_to r full_perm init)
                (pre ** R.pts_to r full_perm init);
        let v = body r () in
        S.assert_ (post v ** exists_ (pts_to #a r #full_perm));
        S.rewrite (post v ** exists_ (pts_to #a r #full_perm))
                  (post v `star` exists_ (pts_to #a r #full_perm));
        let w = S.elim_exists () in
        S.rewrite (pts_to #a r #full_perm w)
                  (R.pts_to #a r full_perm w);
        S.intro_exists_erased w (R.pts_to #a r full_perm);
        S.return v
    in
    let v = R.with_local init body in
    S.return v    

let pts_to_injective_eq (#a:Type0)
                         (#p #q:perm)
                         (#v0 #v1:a)
                         (r:R.ref a)
  : stt_ghost unit emp_inames
      (R.pts_to r p v0 `S.star` R.pts_to r q v1)
      (fun _ -> R.pts_to r p v0 `S.star` R.pts_to r q v0 `S.star` S.pure (v0 == v1))
    = fun _ -> let _ = R.pts_to_injective_eq #a #emp_inames #p #q #v0 #v1 r in ()

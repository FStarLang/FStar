module Pulse.Lib.HigherReference
friend Pulse.Lib.Core
open Steel.ST.Util
open Pulse.Lib.Core
module HR = Steel.ST.HigherReference
module S = Steel.ST.Util

let ref = HR.ref

[@@"__reduce__";"__steel_reduce__"]
let pts_to (#a:Type) (r:ref a) (#[T.exact (`full_perm)] p:perm) (n:a)
  : vprop
  = HR.pts_to r p n


let alloc #a x =
    fun _ ->
        let r = HR.alloc x in
        S.return r

let read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt a
        (HR.pts_to r p n)
        (fun x -> HR.pts_to r p x `star` S.pure (reveal n == x))
  = fun _ ->
        let v = HR.read r in
        S.return v

module T = FStar.Tactics
let ( ! ) #a = read #a

let ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  : stt unit
        (pts_to r #full_perm n)
        (fun _ -> pts_to r #full_perm (hide x))
   = fun _ ->
        HR.write r x;
        S.return ()

let free #a (r:ref a) (#n:erased a)
    = fun _ ->
        HR.free r;
        S.return ()

let share #a r #v #p
  = fun _ -> HR.share r; ()

let gather' (#a:Type) #inames (r:HR.ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit inames
      (HR.pts_to r p0 x0 `S.star` HR.pts_to r p1 x1)
      (fun _ -> HR.pts_to r (sum_perm p0 p1) x0 `S.star` S.pure (x0 == x1))
  = fun _ -> let _ = HR.gather p1 r in ()
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

let with_local #a init #pre #ret_t #post body =
  fun _ ->
    let body (r:ref a)
      : STT ret_t
        (pre `star` HR.pts_to r full_perm init)
        (fun v -> post v `star` exists_ (HR.pts_to r full_perm))
      = S.rewrite
                (pre `star` HR.pts_to r full_perm init)
                (pre ** pts_to r init);
        let v = body r () in
        S.rewrite
                (post v ** exists_ (pts_to r))
                (post v `star` exists_ (pts_to r));
        let w = S.elim_exists () in
        S.rewrite (pts_to #a r #full_perm w)
                  (HR.pts_to r full_perm w);
        S.intro_exists_erased w (HR.pts_to #a r full_perm);
        S.return v
    in
    let v = HR.with_local init body in
    S.return v

let pts_to_injective_eq (#a:Type)
                         (#p #q:perm)
                         (#v0 #v1:a)
                         (r:HR.ref a)
  : stt_ghost unit emp_inames
      (HR.pts_to r p v0 `S.star` HR.pts_to r q v1)
      (fun _ -> HR.pts_to r p v0 `S.star` HR.pts_to r q v0 `S.star` S.pure (v0 == v1))
    = fun _ -> let _ = HR.pts_to_injective_eq #a #emp_inames #p #q #v0 #v1 r in ()

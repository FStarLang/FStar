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

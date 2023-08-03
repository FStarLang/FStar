module Pulse.Lib.Reference
friend Pulse.Lib.Core
open Steel.ST.Util
open Pulse.Lib.Core
module R = Steel.ST.Reference
module S = Steel.ST.Util
let ref = R.ref

[@@"__reduce__";"__steel_reduce__"]
let pts_to = R.pts_to

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
        (pts_to r full_perm n) 
        (fun _ -> pts_to r full_perm (hide x))
   = fun _ ->
        R.write r x;
        S.return ()

let free #a (r:ref a) (#n:erased a)
    = fun _ ->
        R.free r;
        S.return ()

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
        S.rewrite
                (post v ** exists_ (R.pts_to r full_perm))
                (post v `star` exists_ (R.pts_to r full_perm));
        S.return v
    in
    let v = R.with_local init body in
    S.return v    
    
    
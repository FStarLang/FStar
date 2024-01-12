(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

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
        (fun x -> R.pts_to r p n `star` S.pure (reveal n == x))
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
  = fun _ -> R.gather p1 r; ()

let share2 (#a:Type) (r:ref a) (#v:erased a)
  : stt_ghost unit emp_inames
      (pts_to r v)
      (fun _ -> pts_to r #one_half v ** pts_to r #one_half v)
  = share #a r #v

let gather2' (#a:Type) (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit emp_inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r #(sum_perm one_half one_half) x0 ** pure (x0 == x1))
  = gather r

let gather2 (#a:Type) (r:ref a) (#x0 #x1:erased a)
  : Tot (stt_ghost unit emp_inames
           (pts_to r #one_half x0 ** pts_to r #one_half x1)
           (fun _ -> pts_to r #full_perm x0 ** pure (x0 == x1)))
=
  assert (
    stt_ghost unit emp_inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r #(sum_perm one_half one_half) x0 ** pure (x0 == x1))
    ==
    stt_ghost unit emp_inames
      (pts_to r #one_half x0 ** pts_to r #one_half x1)
      (fun () -> pts_to r #full_perm x0 ** pure (x0 == x1))
  ) by (l_to_r [`double_one_half]);
  (* NB: I'm surprised this works without extensionality and a restricted_t... bug? *)
  coerce_eq () (gather2' #a r #x0 #x1 <: stt_ghost _ _ _ _)

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

let cas_u32 (#uses:inames)
        (v:Ghost.erased U32.t)
        (r:ref U32.t)
        (v_old v_new:U32.t)
  : STAtomicT (b:bool{b <==> (Ghost.reveal v == v_old)})
      uses
      (R.pts_to r full_perm v)
      (fun b -> cond b (R.pts_to r full_perm v_new) (R.pts_to r full_perm v))
  = R.cas_u32 #uses v r v_old v_new
  
let cas (r:ref U32.t)
        (u v:U32.t)
        (#i:erased U32.t)
  = fun #ictx _ ->
      let b = cas_u32 #ictx i r u v in
      if b
      then (
        S.rewrite (cond b _ _)
                  (R.pts_to r full_perm v);
        S.intro_pure (reveal i == u);
        S.rewrite (R.pts_to r full_perm v `star` pure (reveal i == u))
                  (cond b (pts_to r #full_perm v ** pure (reveal i == u))
                          (pts_to r #full_perm i));
        S.return b
      )
      else (
        S.rewrite (cond b _ _)
                  (cond b (R.pts_to r full_perm v ** pure (reveal i == u)) (R.pts_to r full_perm i));       
        S.return b
      )

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
    = fun #ictx _ -> let _ = R.pts_to_injective_eq #a #ictx #p #q #v0 #v1 r in ()

let pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p `lesser_equal_perm` full_perm))
  = fun #ictx _ ->
       let _ = R.pts_to_perm #a #ictx #p #v r in
       S.intro_pure (p `lesser_equal_perm` full_perm);
       S.rewrite (pts_to r #p v `star` pure (p `lesser_equal_perm` full_perm))
                 (pts_to r #p v ** pure (p `lesser_equal_perm` full_perm));
       ()

module Pulse.Lib.Par.Pledge.Simple

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Stick
module P = Pulse.Lib.Par.Pledge

let pledge (f:vprop) (v:vprop) : vprop =
  P.pledge_any f v

(* helpers, repeated from Pulse.Lib.Par.Pledge *)
let comm_pre (#a:Type0) (#o:inames) (#pre1 #pre2 : vprop) (#post : a -> vprop)
  (f : stt_ghost a o (pre1 ** pre2) post)
     : stt_ghost a o (pre2 ** pre1) post
=
  sub_stt_ghost _ _ (vprop_equiv_comm _ _)
                    (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
                     f

let comm_post (#a:Type0) (#o:inames) (#pre : vprop) (#post1 #post2 : a -> vprop)
  (f : stt_ghost a o pre (fun x -> post1 x ** post2 x))
     : stt_ghost a o pre (fun x -> post2 x ** post1 x)
=
  sub_stt_ghost _ _ (vprop_equiv_refl _)
                    (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_comm _ _))
                     f

(* sigh *)
let assoc_l_pre (#t:Type0) (#o:inames) (#a #b #c : vprop) (#post : t -> vprop)
  (f : stt_ghost t o (a ** (b ** c)) post)
     : stt_ghost t o ((a ** b) ** c) post
=
  sub_stt_ghost _ _ (vprop_equiv_sym _ _ (vprop_equiv_assoc _ _ _))
                    (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
                     f

inline_for_extraction
val frame_stt_ghost_left
  (#a:Type0)
  (#opens:inames)
  (#pre:vprop) (#post:a -> vprop)
  (frame:vprop)
  (e:stt_ghost a opens pre post)
  : stt_ghost a opens (frame ** pre) (fun x -> frame ** post x)
let frame_stt_ghost_left #a #opens #pre #post frame e =
  let e : stt_ghost a opens (pre ** frame) (fun x -> post x ** frame) =
    frame_stt_ghost frame e
  in
  let e : stt_ghost a opens (frame ** pre) (fun x -> post x ** frame) =
    comm_pre e
  in
  let e : stt_ghost a opens (frame ** pre) (fun x -> frame ** post x) =
    comm_post e
  in
  e

(* Anything that holds now holds in the future too. *)
```pulse
ghost
fn __return_pledge (f v : vprop)
     requires v
     ensures pledge f v
{
  P.return_pledge emp_inames f v;
  fold P.pledge_any;
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn __make_pledge (#os:inames) (f v extra : vprop)
               (k : (unit -> stt_ghost unit os (f ** extra) (fun _ -> f ** v)))
  requires extra
  ensures pledge f v
{
  P.make_pledge os f v extra k;
  fold P.pledge_any;
  fold pledge;
}
```
let make_pledge #os f v extra k = __make_pledge #os f v extra k

// FIXME: marking this ghost gives an awful error, but it should just
// fail saying that `is` is not `emp_inames`
//
// - Tactic logged issue:
// - refl_check_prop_validity failed (not a prop):  Top ()
//   > top (Prims.squash (Pulse.Lib.Core.inames_subset Pulse.Lib.Core.emp_inames (FStar.Ghost.reveal _)))
//   >> app arg (Pulse.Lib.Core.inames_subset Pulse.Lib.Core.emp_inames (FStar.Ghost.reveal _))
//   >>> app arg (FStar.Ghost.reveal _)
//   >>>> app arg (_)
//   Variable not found: _#6
```pulse
fn __redeem_pledge (f v : vprop)
      requires f ** pledge f v
      ensures f ** v
{
  unfold (pledge f v);
  unfold (P.pledge_any f v);
  with is. assert (P.pledge is f v);
  P.redeem_pledge is f v
}
```
let redeem_pledge = __redeem_pledge

```pulse
ghost
fn __bind_pledge (#os : inames) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun () -> f ** pledge f v2)))
   requires pledge f v1 ** extra
    ensures pledge f v2
{
  unfold (pledge f v1);
  unfold (P.pledge_any f v1);
  with is. assert (P.pledge is f v1);
  
  let invs = join_inames is os;
  pledge_sub_inv is invs f v1;
  assert (P.pledge invs f v1);
  
  (* This is just a subtyping of `k`. Once lambdas land this should
  be easy to write. *)
  let k' : (unit -> stt_ghost unit invs (f ** extra ** v1) (fun () -> f ** P.pledge invs f v2)) =
    admit();
  
  P.bind_pledge #invs #f #v1 #v2 extra k';

  fold P.pledge_any;
  fold pledge;
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
ghost
fn __bind_pledge' (#os : inames) (#f #v1 #v2 : vprop)
       (extra : vprop)
       (k : (unit -> stt_ghost unit os (extra ** v1) (fun () -> pledge f v2)))
   requires pledge f v1 ** extra
    ensures pledge f v2
{
  bind_pledge #os #f #v1 #v2 extra (fun () -> assoc_l_pre (frame_stt_ghost_left f (k ())))
}
```
let bind_pledge' = __bind_pledge'

```pulse
ghost
fn __join_pledge (#f v1 v2 : vprop)
  requires pledge f v1 ** pledge f v2
  ensures pledge f (v1 ** v2)
{
  unfold pledge;
  unfold pledge;
  unfold P.pledge_any;
  unfold P.pledge_any;
  
  with is1. assert (P.pledge is1 f v1);
  with is2. assert (P.pledge is2 f v2);
  
  let is = join_inames is1 is2;
  
  pledge_sub_inv is1 is f v1;
  pledge_sub_inv is2 is f v2;

  P.join_pledge #is #f v1 v2;

  fold P.pledge_any;
  fold pledge;
}
```
let join_pledge = __join_pledge

```pulse
ghost
fn __split_pledge (#f v1 v2 : vprop)
  requires pledge f (v1 ** v2)
  ensures pledge f v1 ** pledge f v2
{
  unfold pledge;
  unfold P.pledge_any;
  
  with is. assert (P.pledge is f (v1 ** v2));
  
  P.split_pledge #is #f v1 v2;

  fold P.pledge_any;
  fold P.pledge_any;
  fold pledge;
  fold pledge;
}
```
let split_pledge = __split_pledge

```pulse
ghost
fn __rewrite_pledge (#os : inames) (#f : vprop) (v1 v2 : vprop)
   (k : (unit -> stt_ghost unit os v1 (fun _ -> v2)))
   requires pledge f v1
    ensures pledge f v2
{
  unfold pledge;
  unfold P.pledge_any;
  with is. assert (P.pledge is f v1);
  
  let invs = join_inames is os;
  
  pledge_sub_inv is invs f v1;

  (* Again: This is just a subtyping of `k`. Once lambdas land this should
  be easy to write. *)
  let k' : (unit -> stt_ghost unit invs v1 (fun () -> v2)) =
    admit();
  P.rewrite_pledge #invs #f v1 v2 k';

  fold P.pledge_any;
  fold pledge;
}
```
let rewrite_pledge = __rewrite_pledge

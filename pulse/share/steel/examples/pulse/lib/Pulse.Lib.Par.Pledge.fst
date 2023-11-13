module Pulse.Lib.Par.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open Pulse.Lib.Stick

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

(* A pledge is just a magic stick that preserves the antecedent. *)
(* TODO: can this really be a ghost step? would we ever need to allocate invariants
to redeem? We only need to allocate in split_pledge so far, but that's an operation
that happens outside of the internal ghost step. *)
let pledge opens f v = (@==>) #opens f (f ** v)

let pledge_sub_inv (os1:inames) (os2:inames{inames_subset os1 os2}) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge os1 f v) (fun _ -> pledge os2 f v)
  = stick_sub_inv _ _

let return_pledge os f v =
  intro_stick #os f (f ** v) v
    (fun () ->
      let ff : stt_ghost unit os (f ** v) (fun _ -> f ** v) =
        sub_invs_stt_ghost (return_stt_ghost_noeq () (fun _ -> f ** v)) ()
      in
      let ff : stt_ghost unit os (v ** f) (fun _ -> f ** v) =
        comm_pre ff
      in
      ff)

let make_pledge opens f v extra k =
  intro_stick #opens f (f ** v) extra
    (fun () -> comm_pre (k ()))

let redeem_pledge opens f v =
  comm_pre (elim_stick #opens f (f ** v))

```pulse
ghost
fn bind_pledge_aux
  (os : inames)
  (f v1 v2 extra : vprop)
  (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun _ -> f ** pledge os f v2)))
  (_:unit)
  requires f  ** (extra ** pledge os f v1)
  returns _:unit
  ensures f ** v2
  opens os
{
  redeem_pledge os f v1;
  k ();
  redeem_pledge os f v2
}
```

(* If v1 will hold in the future, and if we can in the future make a
pledge that v2 will hold given v1, then we can pledge v2 with the
same deadline. *)
```pulse
ghost
fn __bind_pledge
  (#os : inames)
  (#f #v1 #v2 : vprop)
  (extra : vprop)
  (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun _ -> f ** pledge os f v2)))
  requires pledge os f v1 ** extra
  returns _:unit
  ensures pledge os f v2
{
  let k
    : (unit -> stt_ghost unit os (f ** (extra ** pledge os f v1))
                                      (fun _ -> f ** v2))
    = bind_pledge_aux os f v1 v2 extra k;
  make_pledge os f v2 (extra ** pledge os f v1)
      k
}
```

let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

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

let bind_pledge' #os #f #v1 #v2 extra k =
  let k : unit -> stt_ghost unit os (extra ** v1) (fun _ -> pledge os f v2) =
    k
  in
  let k : unit -> stt_ghost unit os (f ** (extra ** v1)) (fun _ -> f ** pledge os f v2) =
    fun () -> frame_stt_ghost_left f (k ())
  in
  let k : unit -> stt_ghost unit os (f ** extra ** v1) (fun _ -> f ** pledge os f v2) =
    fun () -> sub_stt_ghost _ _ 
                  (vprop_equiv_sym _ _ (vprop_equiv_assoc _ _ _))
                  (intro_vprop_post_equiv _ _ (fun _ -> vprop_equiv_refl _))
                  (k ())
  in
  bind_pledge #os #f #v1 #v2 extra k

(* We can define join_pledge (NB: very brittle to write this in plain stt *)
let join_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  : stt_ghost unit
              emp_inames
              (pledge os f v1 ** pledge os f v2)
              (fun () -> pledge os f (v1 ** v2))
  = bind_pledge' #os (pledge os f v2) (fun () ->
    // FIXME: sub_invs_stt_ghost could probably be implicit
    sub_invs_stt_ghost (
      bind_pledge' #os v1 (fun () ->
      sub_invs_stt_ghost (return_pledge os f (v1 ** v2)) ())) ())

(* split_pledge *)
#set-options "--ext pulse:guard_policy=SMTSync"

module GR = Pulse.Lib.GhostReference

let inv_p' (os0 : inames) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
     GR.pts_to r1 #one_half b1
  ** GR.pts_to r2 #one_half b2
  ** (match b1, b2 with
      | false, false -> pledge os0 f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp)

let inv_p (os0 : inames) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) : vprop =
  exists_ (fun b1 -> exists_ (fun b2 -> inv_p' os0 f v1 v2 r1 r2 b1 b2))

```pulse
ghost
fn __elim_l (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p os0 f v1 v2 r1 r2)) (_:unit)
  requires f ** GR.pts_to r1 #one_half false
  ensures f ** v1
  opens (add_inv os0 i)
{
  open Pulse.Lib.GhostReference;
  with_invariants i {
    unfold (inv_p os0 f v1 v2 r1 r2);
    with bb1 bb2.
      assert (inv_p' os0 f v1 v2 r1 r2 bb1 bb2);
    unfold (inv_p' os0 f v1 v2 r1 r2 bb1 bb2);
    let b1 = !r1;
    let b2 = !r2;

    assert (pure (b1 == bb1));
    assert (pure (b2 == bb2));

    gather2 #_ 
      r1
      #false #b1;

    let b1 : bool = stt_ghost_reveal _ b1;
    let b2 : bool = stt_ghost_reveal _ b2;

    if b2 {
      (* The "easy" case: the big pledge has already been claimed
      by the other subpledge, so we just extract our resource. *)
      assert (pts_to r1 false);
      r1 := true;
      rewrite emp ** `@(match false, true with
                 | false, false -> pledge os0 f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as `@(match true, true with
                 | false, false -> pledge os0 f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp) ** v1;

      (* I don't understand why this remains in the ctx, but get rid
      of it as it's just emp *)
      rewrite `@(match true, true with
                 | false, false -> pledge os0 f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as emp;

      share2 #_ r1;
      fold (inv_p' os0 f v1 v2 r1 r2 true true);
      fold (inv_p os0 f v1 v2 r1 r2);
      assert (f ** v1 ** inv_p os0 f v1 v2 r1 r2);
      drop_ (pts_to r1 #one_half true);
      ()
    } else {
      (* The "hard" case: the big pledge has not been claimed.
      Claim it, split it, and store the leftover in the invariant. *)
      assert (pts_to r1 false);
      // assert (pts_to r2 false);

      rewrite `@(match false, false with
                 | false, false -> pledge os0 f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp)
           as pledge os0 f (v1 ** v2);

      redeem_pledge os0 f (v1 ** v2);

      assert (f ** v1 ** v2);

      r1 := true;

      rewrite v2
           as `@(match true, false with
                 | false, false -> pledge os0 f (v1 ** v2)
                 | false, true -> v1
                 | true, false -> v2
                 | true, true -> emp);

      share2 #_ r1;
      fold (inv_p' os0 f v1 v2 r1 r2 true false);
      fold (inv_p os0 f v1 v2 r1 r2);
      assert (f ** v1 ** inv_p os0 f v1 v2 r1 r2);
      drop_ (pts_to r1 #one_half true);
      ()
    }
  }
}
```

```pulse
ghost
fn __elim_r (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p os0 f v1 v2 r1 r2)) (_:unit)
  requires f ** GR.pts_to r2 #one_half false
  ensures f ** v2
  opens (add_inv os0 i)
{
  admit ()
}
```

(* bogus.. this is an unobservable step, not ghost. Need to add support
for unobservable in the checker. *)
assume
val new_invariant_ghost #opened (p:vprop) : stt_ghost (inv p) opened p (fun _ -> emp)

```pulse
ghost
fn __split_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge os f (v1 ** v2)
  returns i:iname
  ensures pledge (add_iname os i) f v1 ** pledge (add_iname os i) f v2
{
   let r1 = GR.alloc false;
   let r2 = GR.alloc false;
   GR.share2 #_ r1;
   GR.share2 #_ r2;

   rewrite (pledge os f (v1 ** v2))
        as `@(match false, false with
            | false, false -> pledge os f (v1 ** v2)
            | false, true -> v1
            | true, false -> v2
            | true, true -> emp);

  assert (
     GR.pts_to r1 #one_half false
  ** GR.pts_to r2 #one_half false
  ** `@(match false, false with
      | false, false -> pledge os f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp));

  fold (inv_p' os f v1 v2 r1 r2 false false);
  fold (inv_p os f v1 v2 r1 r2);

  let i = new_invariant_ghost #emp_inames (inv_p os f v1 v2 r1 r2);

  make_pledge
    (add_inv os i)
    f
    v1
    (GR.pts_to r1 #one_half false)
    (__elim_l #os #f v1 v2 r1 r2 i);

  make_pledge
    (add_inv os i)
    f
    v2
    (GR.pts_to r2 #one_half false)
    (__elim_r #os #f v1 v2 r1 r2 i);

  let iname = name_of_inv i;
  
  rewrite (pledge (add_inv os i) f v1)
       as (pledge (add_iname os iname) f v1);
  rewrite (pledge (add_inv os i) f v2)
       as (pledge (add_iname os iname) f v2);
  
  iname
}
```

let split_pledge = __split_pledge

(* /split_pledge *)

let rewrite_pledge (#os:inames) (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : unit -> stt_ghost unit os v1 (fun _ -> v2))
  : stt_ghost unit
              emp_inames
              (pledge os f v1)
              (fun _ -> pledge os f v2)
= bind_sttg #_ #_ #emp_inames
    (rewrite (pledge os f v1) (pledge os f v1 ** emp)
       (vprop_equiv_trans _ _ _
         (vprop_equiv_sym _ _ (vprop_equiv_unit (pledge os f v1)))
         (vprop_equiv_comm _ _)))
    (fun () ->
      bind_pledge' #os #f #v1 #v2 emp (fun () ->
          bind_sttg #_ #_ #os (sub_invs_stt_ghost #_ #emp_inames #os (rewrite (emp ** v1) v1 (vprop_equiv_unit v1)) ()) (fun () ->
          bind_sttg #_ #_ #os (k ()) (fun () ->
          sub_invs_stt_ghost #_ #emp_inames #os (return_pledge os f v2) ()))
    ))

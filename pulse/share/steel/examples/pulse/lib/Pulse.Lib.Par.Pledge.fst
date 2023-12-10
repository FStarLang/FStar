module Pulse.Lib.Par.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

(* A pledge is just a magic stick that preserves the antecedent. *)
(* TODO: can this really be a ghost step? would we ever need to allocate invariants
to redeem? We only need to allocate in split_pledge so far, but that's an operation
that happens outside of the internal ghost step. *)
let pledge opens f v = (@==>) #opens f (f ** v)

let pledge_sub_inv (os1:inames) (os2:inames{inames_subset os1 os2}) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge os1 f v) (fun _ -> pledge os2 f v)
  = stick_sub_inv _ _

```pulse
ghost
fn return_pledge_aux (os:inames) (f v : vprop) ()
    requires v ** f
    ensures f ** v
    opens os
{ () }
```

```pulse
ghost
fn __return_pledge (os:inames) (f v : vprop)
  requires v
  ensures pledge os f v
{
  intro_stick #os f (f ** v) v (return_pledge_aux os f v);
  fold (op_At_Equals_Equals_Greater #os f (f ** v)); // :-(
  fold (pledge os f v);
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn make_pledge_aux (os:inames) (f v extra : vprop)
                 (k : (unit -> stt_ghost unit os (f ** extra) (fun _ -> f ** v)))
                 ()
    requires extra ** f
    ensures f ** v
    opens os
{ 
  k ();
}
```

```pulse
ghost
fn __make_pledge (os:inames) (f v extra : vprop)
                 (k : (unit -> stt_ghost unit os (f ** extra) (fun _ -> f ** v)))
  requires extra
  ensures pledge os f v
{
  intro_stick #os f (f ** v) extra (make_pledge_aux os f v extra k);
  fold (op_At_Equals_Equals_Greater #os f (f ** v)); // :-(
  fold (pledge os f v);
}
```
let make_pledge os f v extra k = __make_pledge os f v extra k

```pulse
ghost
fn __redeem_pledge (os : inames) (f v : vprop)
  requires f ** pledge os f v
  ensures f ** v
  opens os
{
  unfold (pledge os f v);
  unfold (op_At_Equals_Equals_Greater #os f (f ** v)); // :-(
  elim_stick #os f (f ** v);
}
```
let redeem_pledge = __redeem_pledge

```pulse
ghost
fn bind_pledge_aux
  (os : inames)
  (f v1 v2 extra : vprop)
  (k : (unit -> stt_ghost unit os (f ** extra ** v1) (fun _ -> f ** pledge os f v2)))
  ()
  requires f  ** (extra ** pledge os f v1)
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
  ensures pledge os f v2
{
  make_pledge os f v2 (extra ** pledge os f v1) (bind_pledge_aux os f v1 v2 extra k);
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
// just frames f to the left
ghost
fn __bind_pledge'_aux
  (os : inames)
  (f v1 v2 : vprop)
  (extra : vprop)
  (k : (unit -> stt_ghost unit os (extra ** v1) (fun _ -> pledge os f v2)))
  ()
  requires f ** extra ** v1
  ensures f ** pledge os f v2
  opens os
{
  k();
}
```

```pulse
ghost
fn __bind_pledge'
  (#os : inames)
  (#f #v1 #v2 : vprop)
  (extra : vprop)
  (k : (unit -> stt_ghost unit os (extra ** v1) (fun _ -> pledge os f v2)))
  requires pledge os f v1 ** extra
  ensures pledge os f v2
{
  bind_pledge #os #f #v1 #v2 extra (__bind_pledge'_aux os f v1 v2 extra k)
}
```
let bind_pledge' = __bind_pledge'

```pulse
ghost
fn __join_pledge_aux (os:inames) (f v1 v2 : vprop) ()
  requires f ** (pledge os f v1 ** pledge os f v2)
  ensures f ** (v1 ** v2)
  opens os
{
  redeem_pledge os f v1;
  redeem_pledge os f v2
}
```

```pulse
ghost
fn __join_pledge (#os:inames) (#f v1 v2 : vprop)
  requires pledge os f v1 ** pledge os f v2
  ensures pledge os f (v1 ** v2)
{
  (* Copilot wrote this!!! *)
  make_pledge os f (v1 ** v2) (pledge os f v1 ** pledge os f v2) (__join_pledge_aux os f v1 v2)
}
```
let join_pledge = __join_pledge

(* A big chunk follows for split_pledge *)

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
  exists* b1 b2. inv_p' os0 f v1 v2 r1 r2 b1 b2

```pulse
ghost
fn __elim_l (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p os0 f v1 v2 r1 r2)) ()
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

    gather2 r1;

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

      share2 r1;

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
fn __elim_r (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p os0 f v1 v2 r1 r2)) ()
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
val new_invariant_ghost (p:vprop) : stt_ghost (inv p) emp_inames p (fun _ -> emp)

```pulse
ghost
fn __split_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge os f (v1 ** v2)
  returns i:iname
  ensures pledge (add_iname os i) f v1 ** pledge (add_iname os i) f v2
{
   let r1 = GR.alloc false;
   let r2 = GR.alloc false;
   GR.share2 r1;
   GR.share2 r2;

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

  let i = new_invariant_ghost (inv_p os f v1 v2 r1 r2);

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

```pulse
ghost
fn __rewrite_pledge_aux (os:inames) (f v1 v2 : vprop)
      (k : (unit -> stt_ghost unit os v1 (fun _ -> v2)))
      ()
  requires (f ** emp) ** v1
  ensures  f ** pledge os f v2
  opens os
{ 
  k ();
  return_pledge os f v2;
}
```

```pulse
ghost
fn __rewrite_pledge (#os:inames) (#f v1 v2 : vprop)
      (k : (unit -> stt_ghost unit os v1 (fun _ -> v2)))
  requires pledge os f v1
  ensures  pledge os f v2
{
  bind_pledge emp (__rewrite_pledge_aux os f v1 v2 k)
}
```
let rewrite_pledge = __rewrite_pledge

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

module Pulse.Lib.Par.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

assume
val unobservable_reveal_bool
    (b : erased bool)
: stt_unobservable bool emp_inames emp (fun b' -> pure (reveal b == b'))

(* A pledge is just a magic stick that preserves the antecedent. *)
(* TODO: can this really be a ghost step? would we ever need to allocate invariants
to redeem? We only need to allocate in split_pledge so far, but that's an operation
that happens outside of the internal ghost step. *)
let pledge opens f v = (==>*) #opens f (f ** v)

let pledge_sub_inv (os1:inames) (os2:inames{inames_subset os1 os2}) (f:vprop) (v:vprop)
  : stt_ghost unit emp_inames (pledge os1 f v) (fun _ -> pledge os2 f v)
  = trade_sub_inv _ _

```pulse
unobservable
fn return_pledge_aux (os:inames) (f v : vprop) ()
    requires (v ** f)
    ensures (f ** v)
    opens os
{ () }
```

```pulse
ghost
fn __return_pledge (os:inames) (f v : vprop)
  requires v
  ensures pledge os f v
{
  intro_trade #os f (f ** v) v (return_pledge_aux os f v);
  fold ((==>*) #os f (f ** v));
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
unobservable
fn make_pledge_aux (os:inames) (f v extra : vprop)
                 (k : ustep os (f ** extra) (f ** v))
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
                 (k : ustep os (f ** extra) (f ** v))
  requires extra
  ensures pledge os f v
{
  intro_trade #os f (f ** v) extra (make_pledge_aux os f v extra k);
  fold ((==>*) #os f (f ** v));
  fold pledge;
}
```
let make_pledge os f v extra k = __make_pledge os f v extra k

```pulse
unobservable
fn __redeem_pledge (os : inames) (f v : vprop)
  requires f ** pledge os f v
  ensures f ** v
  opens os
{
  unfold pledge;
  unfold ((==>*) #os f (f ** v));
  elim_trade #os f (f ** v);
}
```
let redeem_pledge = __redeem_pledge

```pulse
unobservable
fn bind_pledge_aux
  (os : inames)
  (f v1 v2 extra : vprop)
  (k : ustep os (f ** extra ** v1) (f ** pledge os f v2))
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
  (k : ustep os (f ** extra ** v1) (f ** pledge os f v2))
  requires pledge os f v1 ** extra
  ensures pledge os f v2
{
  make_pledge os f v2 (extra ** pledge os f v1) (bind_pledge_aux os f v1 v2 extra k);
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
// just frames f to the left
unobservable
fn __bind_pledge'_aux
  (os : inames)
  (f v1 v2 : vprop)
  (extra : vprop)
  (k : ustep os (extra ** v1) (pledge os f v2))
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
  (k : ustep os (extra ** v1) (pledge os f v2))
  requires pledge os f v1 ** extra
  ensures pledge os f v2
{
  bind_pledge #os #f #v1 #v2 extra (__bind_pledge'_aux os f v1 v2 extra k)
}
```
let bind_pledge' = __bind_pledge'

```pulse
unobservable
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
unobservable
fn __elim_l (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
            (i : inv (inv_p os0 f v1 v2 r1 r2){not (mem_inv os0 i)})
            ()
  requires f ** GR.pts_to r1 #one_half false
  ensures f ** v1
  opens (add_inv os0 i)
{
  open Pulse.Lib.GhostReference;
  with_invariants (i <: inv _) {
    unobservable
    fn thunk ()
    requires f ** GR.pts_to r1 #one_half false ** inv_p os0 f v1 v2 r1 r2
    ensures (f ** v1 ** inv_p os0 f v1 v2 r1 r2)
    opens os0
    {
      unfold inv_p;
      unfold inv_p';

      gather2 r1;

      let b1 = !r1;
      let b2 = !r2;

      let b1 : bool = unobservable_reveal_bool b1;
      let b2 : bool = unobservable_reveal_bool b2;

      if b2 {
        (* The "easy" case: the big pledge has already been claimed
        by the other subpledge, so we just extract our resource. *)
        assert (pts_to r1 false);
        r1 := true;
        rewrite emp ** (match false, true with
                  | false, false -> pledge os0 f (v1 ** v2)
                  | false, true -> v1
                  | true, false -> v2
                  | true, true -> emp)
            as (match true, true with
                  | false, false -> pledge os0 f (v1 ** v2)
                  | false, true -> v1
                  | true, false -> v2
                  | true, true -> emp) ** v1;

        (* This should just disappear when we start normalizing
        the context. *)
        rewrite (match true, true with
                  | false, false -> pledge os0 f (v1 ** v2)
                  | false, true -> v1
                  | true, false -> v2
                  | true, true -> emp)
            as emp;

        share2 #_ r1;
        fold (inv_p' os0 f v1 v2 r1 r2 true true);
        fold inv_p;
        assert (f ** v1 ** inv_p os0 f v1 v2 r1 r2);
        drop_ (pts_to r1 #one_half true);
      } else {
        (* The "hard" case: the big pledge has not been claimed.
        Claim it, split it, and store the leftover in the invariant. *)
        assert (pts_to r1 false);

        rewrite (match false, false with
                  | false, false -> pledge os0 f (v1 ** v2)
                  | false, true -> v1
                  | true, false -> v2
                  | true, true -> emp)
            as pledge os0 f (v1 ** v2);

        redeem_pledge os0 f (v1 ** v2);

        r1 := true;

        rewrite v2
            as (match true, false with
                  | false, false -> pledge os0 f (v1 ** v2)
                  | false, true -> v1
                  | true, false -> v2
                  | true, true -> emp);

        share2 r1;

        fold (inv_p' os0 f v1 v2 r1 r2 true false);
        fold inv_p;
        assert (f ** v1 ** inv_p os0 f v1 v2 r1 r2);
        drop_ (pts_to r1 #one_half true)
      }
    };
    thunk ()
  }
}
```

```pulse
unobservable
fn __elim_r (#os0:inames) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool) (i : inv (inv_p os0 f v1 v2 r1 r2)) ()
  requires f ** GR.pts_to r2 #one_half false
  ensures f ** v2
  opens (add_inv os0 i)
{
  (* Idem __elim_l *)
  admit ()
}
```

```pulse
unobservable
fn __split_pledge (#os:inames) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge os f (v1 ** v2)
  returns i:(erased iname)
  ensures pledge (add_iname os i) f v1 ** pledge (add_iname os i) f v2
{
   let r1 = GR.alloc false;
   let r2 = GR.alloc false;
   GR.share2 r1;
   GR.share2 r2;

  fold (inv_p' os f v1 v2 r1 r2 false false);
  fold inv_p;

  let i = new_invariant (inv_p os f v1 v2 r1 r2);

  // FIXME: should follow from freshness
  assume_ (pure (not (mem_inv os i)));

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

  let iname = hide (name_of_inv i);

  rewrite each
    add_inv os i
  as
    add_iname os iname;
  
  iname
}
```
let split_pledge = __split_pledge

(* /split_pledge *)

```pulse
unobservable
fn __rewrite_pledge_aux (os:inames) (f v1 v2 : vprop)
      (k : ustep os v1 v2)
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
      (k : ustep os v1 v2)
  requires pledge os f v1
  ensures  pledge os f v2
{
  bind_pledge emp (__rewrite_pledge_aux os f v1 v2 k)
}
```
let rewrite_pledge = __rewrite_pledge

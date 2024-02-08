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
module GR = Pulse.Lib.GhostReference
open Pulse.Class.PtsTo

open FStar.Tactics.V2

let vprop_equiv_refl_eq (v1 v2 : vprop) (_ : squash (v1 == v2)) : vprop_equiv v1 v2 =
  vprop_equiv_refl v1

let __tac () : Tac unit =
  apply (`vprop_equiv_refl_eq)

let pledge opens f v = (==>*) #opens f (f ** v)

let pledge_sub_inv os1 os2 (f:vprop) (v:vprop)
  : stt_ghost unit (pledge os1 f v) (fun _ -> pledge os2 f v)
  = trade_sub_inv _ _

```pulse
ghost
fn return_pledge_aux (is:invlist) (f v : vprop) ()
    requires invlist_v is ** v ** f
    ensures invlist_v is ** (f ** v)
{ () }
```

```pulse
ghost
fn __return_pledge (is:invlist) (f v : vprop)
  requires v
  ensures pledge is f v
{
  intro_trade #is f (f ** v) v (return_pledge_aux is f v);
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn make_pledge_aux
  (is:invlist) (f v extra : vprop)
  (k : ustep is (f ** extra) (f ** v))
  ()
  requires (invlist_v is ** extra) ** f
  ensures invlist_v is ** (f ** v)
{ 
  k ();
}
```

```pulse
ghost
fn __make_pledge
  (is:invlist) (f v extra : vprop)
  (k : ustep is (f ** extra) (f ** v))
  requires extra
  ensures pledge is f v
{
  intro_trade #is f (f ** v) extra (make_pledge_aux is f v extra k);
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```
let make_pledge os f v extra k = __make_pledge os f v extra k

```pulse
ghost
fn __redeem_pledge_ghost (is : invlist) (f v : vprop)
  requires invlist_v is ** f ** pledge is f v
  ensures invlist_v is ** f ** v
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  elim_trade_ghost #is f (f ** v);
}
```
let redeem_pledge_ghost = __redeem_pledge_ghost

```pulse
unobservable
fn __redeem_pledge (is : invlist) (f v : vprop)
  requires f ** pledge is f v
  ensures f ** v
  opens invlist_names is
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  elim_trade #is f (f ** v);
}
```
let redeem_pledge = __redeem_pledge

```pulse
ghost
fn bind_pledge_aux
  (is : invlist)
  (f v1 v2 extra : vprop)
  (k : ustep is (f ** extra ** v1) (f ** pledge is f v2))
  ()
  requires invlist_v is ** (f ** (extra ** pledge is f v1))
  ensures  invlist_v is ** (f ** v2)
{
  redeem_pledge_ghost is f v1;
  k ();
  redeem_pledge_ghost is f v2
}
```

(* If v1 will hold in the future, and if we can in the future make a
pledge that v2 will hold given v1, then we can pledge v2 with the
same deadline. *)
```pulse
ghost
fn __bind_pledge
  (#is : invlist)
  (#f #v1 #v2 : vprop)
  (extra : vprop)
  (k : ustep is (f ** extra ** v1) (f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  make_pledge is f v2 (extra ** pledge is f v1) (bind_pledge_aux is f v1 v2 extra k);
}
```
let bind_pledge #os #f #v1 #v2 extra k = __bind_pledge #os #f #v1 #v2 extra k

```pulse
// just frames f to the left
ghost
fn __bind_pledge'_aux
  (is : invlist)
  (f v1 v2 : vprop)
  (extra : vprop)
  (k : ustep is (extra ** v1) (pledge is f v2))
  ()
  requires invlist_v is ** (f ** extra ** v1)
  ensures  invlist_v is ** (f ** pledge is f v2)
{
  k();
}
```

```pulse
ghost
fn __bind_pledge'
  (#is : invlist)
  (#f #v1 #v2 : vprop)
  (extra : vprop)
  (k : ustep is (extra ** v1) (pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  bind_pledge #is #f #v1 #v2 extra (__bind_pledge'_aux is f v1 v2 extra k)
}
```
let bind_pledge' = __bind_pledge'

```pulse
ghost
fn __rewrite_pledge_full (#is:invlist) (#f v1 v2 : vprop)
      (k : ustep is (f ** v1) (f ** v2))
  requires pledge is f v1
  ensures  pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_v is ** ((f ** emp) ** v1)
    ensures  invlist_v is ** (f ** pledge is f v2)
  {
    k ();
    return_pledge is f v2;
  };
  bind_pledge emp aux
}
```
let rewrite_pledge_full = __rewrite_pledge_full

```pulse
ghost
fn __rewrite_pledge (#is:invlist) (#f v1 v2 : vprop)
      (k : ustep is v1 v2)
  requires pledge is f v1
  ensures  pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_v is ** (f ** v1)
    ensures  invlist_v is ** (f ** v2)
  {
    k()
  };
  rewrite_pledge_full #is #f v1 v2 aux
}
```
let rewrite_pledge = __rewrite_pledge

```pulse
ghost
fn __rewrite_pledge0 (#is:invlist) (#f v1 v2 : vprop)
      (k : ustep0 v1 v2)
  requires pledge is f v1
  ensures  pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_v is ** (f ** v1)
    ensures  invlist_v is ** (f ** v2)
  {
    k()
  };
  rewrite_pledge_full #is #f v1 v2 aux
}
```
let rewrite_pledge0 = __rewrite_pledge0

```pulse
ghost
fn __join_pledge_aux
  (is:invlist) (f v1 v2 : vprop) ()
  requires invlist_v is ** (f ** (pledge is f v1 ** pledge is f v2))
  ensures  invlist_v is ** (f ** (v1 ** v2))
{
  redeem_pledge_ghost is f v1;
  redeem_pledge_ghost is f v2
}
```

```pulse
ghost
fn __join_pledge
  (#is:invlist) (#f v1 v2 : vprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)
{
  (* Copilot wrote this!!! *)
  make_pledge is f (v1 ** v2) (pledge is f v1 ** pledge is f v2) (__join_pledge_aux is f v1 v2)
}
```
let join_pledge = __join_pledge

```pulse
ghost
fn __squash_pledge_aux
  (is:invlist) (f v1 : vprop) ()
  requires invlist_v is ** (f ** (pledge is f (pledge is f v1)))
  ensures  invlist_v is ** (f ** v1)
{
  redeem_pledge_ghost is f (pledge is f v1);
  redeem_pledge_ghost is f v1
}
```

```pulse
ghost
fn __squash_pledge
  (is:invlist) (f v1 : vprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1
{
  make_pledge is f v1 (pledge is f (pledge is f v1)) (__squash_pledge_aux is f v1)
}
```
let squash_pledge = __squash_pledge

```pulse
ghost
fn __squash_pledge'
  (is1 is2 is :invlist) (f v : vprop)
  requires pure (invlist_sub is1 is) **
           pure (invlist_sub is2 is) **
           pledge is1 f (pledge is2 f v)
  ensures pledge is f v
{
  pledge_sub_inv is1 is f (pledge is2 f v);
  rewrite_pledge0 #is #f (pledge is2 f v) (pledge is f v)
    (fun () -> pledge_sub_inv is2 is f v);
  squash_pledge is f v;
}
```
let squash_pledge' = __squash_pledge'

(* A big chunk follows for split_pledge *)

let inv_p' (is:invlist) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
     GR.pts_to r1 #one_half b1
  ** GR.pts_to r2 #one_half b2
  ** (match b1, b2 with
      | false, false -> pledge is f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp)

let inv_p (is:invlist) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) : vprop =
  exists* b1 b2. inv_p' is f v1 v2 r1 r2 b1 b2

```pulse
ghost
fn elim_body_l
  (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
  ()
  requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r1 #one_half false)
  ensures  (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** v1)
{
  open Pulse.Lib.GhostReference;
  unfold inv_p;
  unfold inv_p';

  gather2 r1;

  let b1 = !r1;
  let b2 = !r2;

  let b1 : bool = reveal b1;
  let b2 : bool = reveal b2;

  if b2 {
    (* The "easy" case: the big pledge has already been claimed
    by the other subpledge, so we just extract our resource. *)
    assert (pts_to r1 false);
    r1 := true;
    rewrite emp ** (match false, true with
              | false, false -> pledge is f (v1 ** v2)
              | false, true -> v1
              | true, false -> v2
              | true, true -> emp)
        as (match true, true with
              | false, false -> pledge is f (v1 ** v2)
              | false, true -> v1
              | true, false -> v2
              | true, true -> emp) ** v1;

    (* This should just disappear when we start normalizing
    the context. *)
    rewrite (match true, true with
              | false, false -> pledge is f (v1 ** v2)
              | false, true -> v1
              | true, false -> v2
              | true, true -> emp)
        as emp;

    share2 #_ r1;
    fold (inv_p' is f v1 v2 r1 r2 true true);
    fold inv_p;
    assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
    drop_ (pts_to r1 #one_half true);
  } else {
    (* The "hard" case: the big pledge has not been claimed.
    Claim it, split it, and store the leftover in the invariant. *)
    assert (pts_to r1 false);

    rewrite (match false, false with
              | false, false -> pledge is f (v1 ** v2)
              | false, true -> v1
              | true, false -> v2
              | true, true -> emp)
        as pledge is f (v1 ** v2);

    redeem_pledge_ghost is f (v1 ** v2);

    r1 := true;

    share2 r1;

    fold (inv_p' is f v1 v2 r1 r2 true false);
    fold inv_p;
    assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
    drop_ (pts_to r1 #one_half true)
  }
}
```

```pulse
ghost
fn flip_invp
  (is:invlist) (f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
  requires inv_p is f v1 v2 r1 r2
  ensures  inv_p is f v2 v1 r2 r1
{
  unfold inv_p;

  with b1 b2. assert (inv_p' is f v1 v2 r1 r2 b1 b2);

  unfold inv_p';

  (* This is now true with PulseCore. *)
  let _ = elim_vprop_equiv (vprop_equiv_comm v1 v2);
  assert (pure (v1 ** v2 == v2 ** v1));

  rewrite_by
     (match b1, b2 with
      | false, false -> pledge is f (v1 ** v2)
      | false, true -> v1
      | true, false -> v2
      | true, true -> emp)
     (match b2, b1 with
      | false, false -> pledge is f (v2 ** v1)
      | false, true -> v2
      | true, false -> v1
      | true, true -> emp)
    __tac
    ();

  fold (inv_p' is f v2 v1 r2 r1 b2 b1);
  fold inv_p;
}
```

```pulse
ghost
fn elim_body_r
  (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
  ()
  requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r2 #one_half false)
  ensures  (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** v2)
{
  flip_invp is f v1 v2 r1 r2;
  elim_body_l #is #f v2 v1 r2 r1 ();
  flip_invp is f v2 v1 r2 r1;
}
```

```pulse
unobservable
fn __split_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
  requires pledge is f (v1 ** v2)
  returns r : (e : invlist_elem { not (mem_inv (invlist_names is) (dsnd e)) })
  ensures pledge (add_one r is) f v1 ** pledge (add_one r is) f v2
{
  let r1 = GR.alloc false;
  let r2 = GR.alloc false;
  GR.share2 r1;
  GR.share2 r2;
  
  fold (inv_p' is f v1 v2 r1 r2 false false);
  fold inv_p;

  let i = new_invariant (inv_p is f v1 v2 r1 r2);
  // FIXME: should follow from freshness
  assume_ (pure (not (mem_inv (invlist_names is) i)));
  
  let pi : invlist_elem = Mkdtuple2 #vprop #(fun p -> inv p) (inv_p is f v1 v2 r1 r2) i;

  let is' : invlist = add_one pi is;

  make_pledge
    is'
    f
    v1
    (GR.pts_to r1 #one_half false)
    (elim_body_l #is #f v1 v2 r1 r2);

  make_pledge
    is'
    f
    v2
    (GR.pts_to r2 #one_half false)
    (elim_body_r #is #f v1 v2 r1 r2);

  rewrite each
    is'
  as
    add_one pi is;

  pi
}
```
let split_pledge = __split_pledge

(* /split_pledge *)

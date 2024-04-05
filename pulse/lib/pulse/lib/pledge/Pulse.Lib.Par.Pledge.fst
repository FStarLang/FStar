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

let pledge_sub_inv os1 os2 (f:vprop) (v:vprop) = trade_sub_inv _ _

```pulse
ghost
fn __return_pledge (is:invlist) (f v : vprop)
  requires invlist_inv is ** v
  ensures pledge is f v
{
  ghost
  fn aux ()
    requires invlist_inv is ** v ** f
    ensures invlist_inv is ** (f ** v)
    opens (invlist_names is)
  {
    ()
  };
  intro_trade #is f (f ** v) v aux;
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```
let return_pledge = __return_pledge

```pulse
ghost
fn __make_pledge
  (is:invlist) (f v extra : vprop)
  (k : ustep is (f ** extra) (f ** v))
  requires invlist_inv is ** extra
  ensures pledge is f v
{
  ghost
  fn aux ()
    requires invlist_inv is ** extra ** f
    ensures invlist_inv is ** (f ** v)
    opens (invlist_names is)
  {
    k ()
  };

  intro_trade #is f (f ** v) extra aux;
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```
let make_pledge os f v extra k = __make_pledge os f v extra k  // eta-expansion to account for $ on k

```pulse
ghost
fn __redeem_pledge (is : invlist) (f v : vprop)
  requires f ** pledge is f v
  ensures f ** v ** invlist_inv is
  opens (invlist_names is)
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  elim_trade #is f (f ** v);
}
```
let redeem_pledge = __redeem_pledge

```pulse
ghost
fn pledge_invs_aux (is:invlist) (f:vprop) (v:vprop)
  requires pledge is f v
  ensures pledge is f v ** invlist_inv is
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  trade_invs ();
  fold ((==>*) #is f (f ** v));
  fold pledge
}
```

let pledge_invs = pledge_invs_aux

```pulse
ghost
fn squash_pledge_aux (is:invlist) (f:vprop) (v1:vprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** pledge is f (pledge is f v1))
    ensures invlist_inv is ** (f ** v1)
    opens (invlist_names is)
  {
    redeem_pledge is f (pledge is f v1);
    drop_ (invlist_inv is);
    redeem_pledge is f v1;
    drop_ (invlist_inv is)

  };
  pledge_invs is f _;
  make_pledge is f v1 (pledge is f (pledge is f v1)) aux
}
```

```pulse
ghost
fn bind_pledge_aux
  (#is : invlist)
  (#f #v1 #v2 extra : vprop)
  (k : ustep is (f ** extra ** v1) (f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** (extra ** pledge is f v1))
    ensures invlist_inv is ** (f ** pledge is f v2)
    opens (invlist_names is)
  {
    redeem_pledge is f v1;
    k ();
    drop_ (invlist_inv is)
  };

  pledge_invs is f v1;
  make_pledge is f (pledge is f v2) (extra ** pledge is f v1) aux;
  squash_pledge_aux is f v2
}
```

let bind_pledge = bind_pledge_aux

```pulse
ghost
fn bind_pledge'_aux
  (#is : invlist)
  (#f #v1 #v2 extra : vprop)
  (k : ustep is (extra ** v1) (pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** extra ** v1)
    ensures invlist_inv is ** (f ** pledge is f v2)
    opens (invlist_names is)
  {
    k ()
  };
  bind_pledge_aux #is #f #v1 #v2 extra aux
}
```

let bind_pledge' = bind_pledge'_aux

```pulse
ghost
fn rewrite_pledge_full_aux
  (#is:invlist)
  (#f v1 v2:vprop)
  (k : ustep is (f ** v1) (f ** v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** pledge is f v1)
    ensures invlist_inv is ** (f ** v2)
    opens (invlist_names is)
  {
    redeem_pledge is f v1;
    k ();
    drop_ (invlist_inv is)
  };
  
  pledge_invs is f v1;
  make_pledge is f v2 (pledge is f v1) aux;
}
```

let rewrite_pledge_full = rewrite_pledge_full_aux

```pulse
ghost
fn rewrite_pledge_aux
  (#is:invlist)
  (#f v1 v2:vprop)
  (k : ustep is v1 v2)
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** v1)
    ensures invlist_inv is ** (f ** v2)
    opens (invlist_names is)
  {
    k ()
  };

  rewrite_pledge_full #is #f v1 v2 aux  
}
```

let rewrite_pledge = rewrite_pledge_aux

```pulse
ghost
fn rewrite_pledge0_aux
  (#is:invlist)
  (#f v1 v2:vprop)
  (k : ustep0 v1 v2)
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** v1)
    ensures invlist_inv is ** (f ** v2)
    opens (invlist_names is)
  {
    k ()
  };

  rewrite_pledge_full #is #f v1 v2 aux  
}
```

let rewrite_pledge0 = rewrite_pledge0_aux

```pulse
ghost
fn join_pledge_aux
  (#is:invlist)
  (#f v1 v2:vprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** (pledge is f v1 ** pledge is f v2))
    ensures invlist_inv is ** (f ** (v1 ** v2))
    opens (invlist_names is)
  {
    redeem_pledge is f v1;
    redeem_pledge is f v2;
    drop_ (invlist_inv is);
    drop_ (invlist_inv is)
  };
  
  pledge_invs is f v1;
  make_pledge is f (v1 ** v2) (pledge is f v1 ** pledge is f v2) aux;
}
```

let join_pledge = join_pledge_aux

let squash_pledge = squash_pledge_aux

```pulse
ghost
fn squash_pledge'_aux
  (is1 is2 is:invlist)
  (f v1:vprop)
  requires invlist_inv is **
           pure (invlist_sub is1 is) **
           pure (invlist_sub is2 is) **
           pledge is1 f (pledge is2 f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires invlist_inv is ** (f ** (pledge is1 f (pledge is2 f v1)))
    ensures invlist_inv is ** (f ** v1)
    opens (invlist_names is)
  {
    redeem_pledge is1 f (pledge is2 f v1);
    redeem_pledge is2 f v1;
    drop_ (invlist_inv is1);
    drop_ (invlist_inv is2)
  };
  
  make_pledge is f v1 (pledge is1 f (pledge is2 f v1)) aux
}
```

let squash_pledge' = squash_pledge'_aux


//
// This proof below requires inv_p to be big ... which I think it is not
//

(* A big chunk follows for split_pledge *)

// let inv_p' (is:invlist) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
//      GR.pts_to r1 #one_half b1
//   ** GR.pts_to r2 #one_half b2
//   ** (match b1, b2 with
//       | false, false -> pledge is f (v1 ** v2)
//       | false, true -> v1
//       | true, false -> v2
//       | true, true -> emp)

// let inv_p (is:invlist) (f v1 v2 : vprop) (r1 r2 : GR.ref bool) : vprop =
//   exists* b1 b2. inv_p' is f v1 v2 r1 r2 b1 b2

// ```pulse
// ghost
// fn elim_body_l
//   (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
//   ()
//   requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r1 #one_half false)
//   ensures  (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** v1)
//   opens (invlist_names is)
// {
//   open Pulse.Lib.GhostReference;
//   unfold inv_p;
//   unfold inv_p';

//   gather2 r1;

//   let b1 = !r1;
//   let b2 = !r2;

//   let b1 : bool = reveal b1;
//   let b2 : bool = reveal b2;

//   if b2 {
//     (* The "easy" case: the big pledge has already been claimed
//     by the other subpledge, so we just extract our resource. *)
//     assert (pts_to r1 false);
//     r1 := true;
//     rewrite emp ** (match false, true with
//               | false, false -> pledge is f (v1 ** v2)
//               | false, true -> v1
//               | true, false -> v2
//               | true, true -> emp)
//         as (match true, true with
//               | false, false -> pledge is f (v1 ** v2)
//               | false, true -> v1
//               | true, false -> v2
//               | true, true -> emp) ** v1;

//     (* This should just disappear when we start normalizing
//     the context. *)
//     rewrite (match true, true with
//               | false, false -> pledge is f (v1 ** v2)
//               | false, true -> v1
//               | true, false -> v2
//               | true, true -> emp)
//         as emp;

//     share2 #_ r1;
//     fold (inv_p' is f v1 v2 r1 r2 true true);
//     fold inv_p;
//     assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
//     drop_ (pts_to r1 #one_half true);
//   } else {
//     (* The "hard" case: the big pledge has not been claimed.
//     Claim it, split it, and store the leftover in the invariant. *)
//     assert (pts_to r1 false);

//     rewrite (match false, false with
//               | false, false -> pledge is f (v1 ** v2)
//               | false, true -> v1
//               | true, false -> v2
//               | true, true -> emp)
//         as pledge is f (v1 ** v2);

//     redeem_pledge is f (v1 ** v2);

//     r1 := true;

//     share2 r1;

//     fold (inv_p' is f v1 v2 r1 r2 true false);
//     fold inv_p;
//     assert (f ** v1 ** inv_p is f v1 v2 r1 r2);
//     drop_ (pts_to r1 #one_half true);
//     drop_ (invlist_inv _)
//   }
// }
// ```

// ```pulse
// ghost
// fn flip_invp
//   (is:invlist) (f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
//   requires inv_p is f v1 v2 r1 r2
//   ensures  inv_p is f v2 v1 r2 r1
// {
//   unfold inv_p;

//   with b1 b2. assert (inv_p' is f v1 v2 r1 r2 b1 b2);

//   unfold inv_p';

//   (* This is now true with PulseCore. *)
//   let _ = elim_vprop_equiv (vprop_equiv_comm v1 v2);
//   assert (pure (v1 ** v2 == v2 ** v1));

//   rewrite_by
//      (match b1, b2 with
//       | false, false -> pledge is f (v1 ** v2)
//       | false, true -> v1
//       | true, false -> v2
//       | true, true -> emp)
//      (match b2, b1 with
//       | false, false -> pledge is f (v2 ** v1)
//       | false, true -> v2
//       | true, false -> v1
//       | true, true -> emp)
//     __tac
//     ();

//   fold (inv_p' is f v2 v1 r2 r1 b2 b1);
//   fold inv_p;
// }
// ```

// ```pulse
// ghost
// fn elim_body_r
//   (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop) (r1 r2 : GR.ref bool)
//   ()
//   requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r2 #one_half false)
//   ensures  (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** v2)
//   opens (invlist_names is)
// {
//   flip_invp is f v1 v2 r1 r2;
//   elim_body_l #is #f v2 v1 r2 r1 ();
//   flip_invp is f v2 v1 r2 r1;
// }
// ```

// ```pulse
// ghost
// fn __split_pledge (#is:invlist) (#f:vprop) (v1:vprop) (v2:vprop)
//   requires pledge is f (v1 ** v2)
//   returns r : (e : invlist_elem { not (mem_inv (invlist_names is) (snd e)) })
//   ensures pledge (add_one r is) f v1 ** pledge (add_one r is) f v2
//   opens (invlist_names is)
// {
//   let r1 = GR.alloc false;
//   let r2 = GR.alloc false;
//   GR.share2 r1;
//   GR.share2 r2;
  
//   fold (inv_p' is f v1 v2 r1 r2 false false);
//   fold inv_p;

//   let i = new_invariant (inv_p is f v1 v2 r1 r2);
//   // FIXME: should follow from freshness
//   assume_ (pure (not (mem_inv (invlist_names is) i)));
  
//   // let pi : invlist_elem = Mkdtuple2 #vprop #(fun p -> inv p) (inv_p is f v1 v2 r1 r2) i;

//   // let is' : invlist = add_one pi is;

//   admit ()

//   // make_pledge
//   //   is'
//   //   f
//   //   v1
//   //   (GR.pts_to r1 #one_half false)
//   //   (elim_body_l #is #f v1 v2 r1 r2);

//   // make_pledge
//   //   is'
//   //   f
//   //   v2
//   //   (GR.pts_to r2 #one_half false)
//   //   (elim_body_r #is #f v1 v2 r1 r2);

//   // rewrite each
//   //   is'
//   // as
//   //   add_one pi is;

//   // pi
// }
// ```

// let split_pledge = __split_pledge

// (* /split_pledge *)

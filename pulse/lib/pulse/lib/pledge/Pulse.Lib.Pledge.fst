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

module Pulse.Lib.Pledge

open Pulse.Lib.Pervasives
open Pulse.Lib.Trade

module GR = Pulse.Lib.GhostReference

open FStar.Tactics.V2

let slprop_equiv_refl_eq (v1 v2 : slprop) (_ : squash (v1 == v2)) : slprop_equiv v1 v2 =
  slprop_equiv_refl v1

let __tac () : Tac unit =
  apply (`slprop_equiv_refl_eq)

let pledge is f v = (==>*) #is f (f ** v)

let pledge_sub_inv is1 is2 (f:slprop) (v:slprop) = trade_sub_inv _ _

```pulse
ghost
fn return_pledge (f v : slprop)
  requires v
  ensures pledge emp_inames f v
{
  ghost
  fn aux ()
    requires v ** f
    ensures f ** v
  {
    ()
  };
  intro_trade #emp_inames f (f ** v) v aux;
  fold ((==>*) #emp_inames f (f ** v));
  fold pledge;
}
```

```pulse
ghost
fn make_pledge
  (is:inames) (f v extra:slprop)
  (k:unit -> stt_ghost unit is (f ** extra) (fun _ -> f ** v))
  requires extra
  ensures pledge is f v
{
  ghost
  fn aux ()
    requires extra ** f
    ensures f ** v
    opens is
  {
    k ()
  };

  intro_trade #is f (f ** v) extra aux;
  fold ((==>*) #is f (f ** v));
  fold pledge;
}
```

```pulse
ghost
fn redeem_pledge (is:inames) (f v:slprop)
  requires f ** pledge is f v
  ensures f ** v
  opens is
{
  unfold pledge;
  unfold ((==>*) #is f (f ** v));
  elim_trade #is f (f ** v);
}
```

// ```pulse
// ghost
// fn pledge_invs_aux (is:invlist) (f:slprop) (v:slprop)
//   requires pledge is f v
//   ensures pledge is f v ** invlist_inv is
// {
//   unfold pledge;
//   unfold ((==>*) #is f (f ** v));
//   trade_invs ();
//   fold ((==>*) #is f (f ** v));
//   fold pledge
// }
// ```

// let pledge_invs = pledge_invs_aux

```pulse
ghost
fn squash_pledge (is:inames) (f:slprop) (v1:slprop)
  requires pledge is f (pledge is f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** pledge is f (pledge is f v1)
    ensures f ** v1
    opens is
  {
    redeem_pledge is f (pledge is f v1);
    redeem_pledge is f v1
  };
  make_pledge is f v1 (pledge is f (pledge is f v1)) aux
}
```

```pulse
ghost
fn bind_pledge
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** extra ** v1) (fun _ -> f ** pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** (extra ** pledge is f v1)
    ensures f ** pledge is f v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };

  make_pledge is f (pledge is f v2) (extra ** pledge is f v1) aux;
  squash_pledge is f v2
}
```

```pulse
ghost
fn bind_pledge'
  (#is:inames)
  (#f #v1 #v2 extra:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (extra ** v1) (fun _ -> pledge is f v2))
  requires pledge is f v1 ** extra
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** extra ** v1
    ensures f ** pledge is f v2
    opens is
  {
    k ()
  };
  bind_pledge #is #f #v1 #v2 extra aux
}
```

```pulse
ghost
fn rewrite_pledge_full
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k (f ** v1) (fun _ -> f ** v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** pledge is f v1
    ensures f ** v2
    opens is
  {
    redeem_pledge is f v1;
    k ()
  };
  
  make_pledge is f v2 (pledge is f v1) aux;
}
```

```pulse
ghost
fn rewrite_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  (#is_k:inames { inames_subset is_k is })
  (k:unit -> stt_ghost unit is_k v1 (fun _ -> v2))
  requires pledge is f v1
  ensures pledge is f v2
{
  ghost
  fn aux ()
    requires f ** v1
    ensures f ** v2
    opens is
  {
    k ()
  };

  rewrite_pledge_full #is #f v1 v2 aux  
}
```

```pulse
ghost
fn join_pledge
  (#is:inames)
  (#f v1 v2:slprop)
  requires pledge is f v1 ** pledge is f v2
  ensures pledge is f (v1 ** v2)
{
  ghost
  fn aux ()
    requires f ** (pledge is f v1 ** pledge is f v2)
    ensures f ** (v1 ** v2)
    opens is
  {
    redeem_pledge is f v1;
    redeem_pledge is f v2;
  };
  
  make_pledge is f (v1 ** v2) (pledge is f v1 ** pledge is f v2) aux;
}
```

```pulse
ghost
fn squash_pledge'
  (is1 is2 is:inames)
  (f v1:slprop)
  requires pure (inames_subset is1 is) **
           pure (inames_subset is2 is) **
           pledge is1 f (pledge is2 f v1)
  ensures pledge is f v1
{
  ghost
  fn aux ()
    requires f ** (pledge is1 f (pledge is2 f v1))
    ensures f ** v1
    opens is
  {
    redeem_pledge is1 f (pledge is2 f v1);
    redeem_pledge is2 f v1
  };
  
  make_pledge is f v1 (pledge is1 f (pledge is2 f v1)) aux
}
```

//
// This proof below requires inv_p to be big ...
//

(* A big chunk follows for split_pledge *)

// let inv_p' (is:invlist) (f v1 v2 : slprop) (r1 r2 : GR.ref bool) (b1 b2 : bool) =
//      GR.pts_to r1 #0.5R b1
//   ** GR.pts_to r2 #0.5R b2
//   ** (match b1, b2 with
//       | false, false -> pledge is f (v1 ** v2)
//       | false, true -> v1
//       | true, false -> v2
//       | true, true -> emp)

// let inv_p (is:invlist) (f v1 v2 : slprop) (r1 r2 : GR.ref bool) : slprop =
//   exists* b1 b2. inv_p' is f v1 v2 r1 r2 b1 b2

// ```pulse
// ghost
// fn elim_body_l
//   (#is:invlist) (#f:slprop) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
//   ()
//   requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r1 #0.5R false)
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
//     drop_ (pts_to r1 #0.5R true);
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
//     drop_ (pts_to r1 #0.5R true);
//     drop_ (invlist_inv _)
//   }
// }
// ```

// ```pulse
// ghost
// fn flip_invp
//   (is:invlist) (f:slprop) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
//   requires inv_p is f v1 v2 r1 r2
//   ensures  inv_p is f v2 v1 r2 r1
// {
//   unfold inv_p;

//   with b1 b2. assert (inv_p' is f v1 v2 r1 r2 b1 b2);

//   unfold inv_p';

//   (* This is now true with PulseCore. *)
//   let _ = elim_slprop_equiv (slprop_equiv_comm v1 v2);
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
//   (#is:invlist) (#f:slprop) (v1:slprop) (v2:slprop) (r1 r2 : GR.ref bool)
//   ()
//   requires (inv_p is f v1 v2 r1 r2 ** invlist_v is) ** (f ** GR.pts_to r2 #0.5R false)
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
// fn __split_pledge (#is:invlist) (#f:slprop) (v1:slprop) (v2:slprop)
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
  
//   // let pi : invlist_elem = Mkdtuple2 #slprop #(fun p -> inv p) (inv_p is f v1 v2 r1 r2) i;

//   // let is' : invlist = add_one pi is;

//   admit ()

//   // make_pledge
//   //   is'
//   //   f
//   //   v1
//   //   (GR.pts_to r1 #0.5R false)
//   //   (elim_body_l #is #f v1 v2 r1 r2);

//   // make_pledge
//   //   is'
//   //   f
//   //   v2
//   //   (GR.pts_to r2 #0.5R false)
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

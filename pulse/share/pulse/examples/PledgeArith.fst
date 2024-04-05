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

module PledgeArith

(* automation wishlist for pledges *)

open Pulse.Lib.Pervasives
open Pulse.Lib.InvList
module T = Pulse.Lib.Task
open Pulse.Lib.Par.Pledge

```pulse
ghost
fn pledge_return_now (f:vprop) (r : ref int)
  requires pts_to r 123
  ensures pledge [] f (pts_to r 123)
{
  rewrite emp as (invlist_inv []);
  return_pledge [] f (pts_to r 123); // ideally automated
}
```

```pulse
ghost
fn pledge_join (f:vprop) (v1 v2 : vprop)
  requires pledge [] f v1 ** pledge [] f v2
  ensures pledge [] f (v1 ** v2)
{
  join_pledge #[] #f v1 v2; // ideally automated
}
```

```pulse
fn pledge_comm (f:vprop) (v1 v2 : vprop)
  requires pledge [] f (v2 ** v1)
  ensures pledge [] f (v1 ** v2)
{
  // this one can also be proved by relying on the equality between v1**v2 and v2**v1,
  // but that's not a scalable solution
  // let _ = elim_vprop_equiv (vprop_equiv_comm v1 v2);
  ghost
  fn pf (_:unit)
    (* unfortunate: emp (coming from invlist_v []) is needed to make this typecheck.
    Maybe an SMT pattern for emp ** v == v would help? *)
    (* also: a nested function may make this more convenient *)
    requires emp ** (v2 ** v1)
    ensures emp ** (v1 ** v2)
  {
    ()
  };
  rewrite_pledge #[] #f (v2 ** v1) (v1 ** v2) pf;
  
  // if not fully automated (certainly cannot be for all rewrites)
  // maybe some syntax like
  (*
  rewrite_pledge #[] #f (v2 ** v1) (v1 ** v2) {
    ()
  };
  *)
  // where the block is checked at the type of the `pf` function above
}
```

```pulse
ghost
fn pledge_squash (f:vprop) (v1 v2 : vprop)
  requires pledge [] f (pledge [] f v1)
  ensures pledge [] f v1
{
  squash_pledge [] f v1;  // ideally automated
}
```

```pulse
ghost
fn pledge_squash_and_join (f:vprop) (v1 v2 : vprop)
  requires pledge [] f (pledge [] f v1) ** pledge [] f v2
  ensures pledge [] f (v1 ** v2)
{
  squash_pledge [] f v1;  // ideally automated
  join_pledge #[] #f v1 v2; // ideally automated
}
```

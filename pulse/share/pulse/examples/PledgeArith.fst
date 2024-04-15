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
open Pulse.Lib.Pledge

```pulse
ghost
fn pledge_return_now (f:vprop) (r : ref int)
  requires pts_to r 123
  ensures pledge emp_inames f (pts_to r 123)
{
  return_pledge f (pts_to r 123); // ideally automated
}
```

```pulse
ghost
fn pledge_join (f:vprop) (v1 v2 : vprop)
  requires pledge emp_inames f v1 ** pledge emp_inames f v2
  ensures pledge emp_inames f (v1 ** v2)
{
  join_pledge #emp_inames #f v1 v2; // ideally automated
}
```

```pulse
fn pledge_comm (f:vprop) (v1 v2 : vprop)
  requires pledge emp_inames f (v2 ** v1)
  ensures pledge emp_inames f (v1 ** v2)
{
  // this one can also be proved by relying on the equality between v1**v2 and v2**v1,
  // but that's not a scalable solution
  // let _ = elim_vprop_equiv (vprop_equiv_comm v1 v2);
  ghost
  fn pf (_:unit)
    (* a nested function may make this more convenient *)
    requires v2 ** v1
    ensures v1 ** v2
  {
    ()
  };
  rewrite_pledge #emp_inames #f (v2 ** v1) (v1 ** v2) pf;
  
  // if not fully automated (certainly cannot be for all rewrites)
  // maybe some syntax like
  (*
  rewrite_pledge #emp_inames #f (v2 ** v1) (v1 ** v2) {
    ()
  };
  *)
  // where the block is checked at the type of the `pf` function above
}
```

```pulse
ghost
fn pledge_squash (f:vprop) (v1 v2 : vprop)
  requires pledge emp_inames f (pledge emp_inames f v1)
  ensures pledge emp_inames f v1
{
  squash_pledge emp_inames f v1;  // ideally automated
}
```

```pulse
ghost
fn pledge_squash_and_join (f:vprop) (v1 v2 : vprop)
  requires pledge emp_inames f (pledge emp_inames f v1) ** pledge emp_inames f v2
  ensures pledge emp_inames f (v1 ** v2)
{
  squash_pledge emp_inames f v1;  // ideally automated
  join_pledge #emp_inames #f v1 v2; // ideally automated
}
```

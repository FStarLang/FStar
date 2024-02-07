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

module Bug111
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick.Util

//works, lucky, because it appears in the right order in the precondition
```pulse
ghost
fn test_trans (p q r:vprop)
requires (p @==> q) ** (q @==> r)
ensures (p @==> r)
{
    trans _ _ _;
}
```

[@@expect_failure]
```pulse
ghost
fn test_trans_2 (p q r:vprop)
requires (q @==> r) ** (p @==> q)
ensures (p @==> r)
{
    trans _ _ _;
}
```

```pulse
ghost
fn test_elim (p q:vprop)
requires (p @==> q) ** p
ensures q
{
    elim _ _;
}
```

// fails since unification doesn't backtrack, and unifies the first
// precondition of elim with r @==> r and then gets stuck
[@@expect_failure]
```pulse
ghost
fn test_elim_fails (p q r:vprop)
requires (r @==> r) ** p ** (p @==> q)
ensures q ** (r @==> r)
{
    elim _ _;
}
```

//this is the main report in Bug 111
```pulse
ghost
fn test_elim_2 (p q r:vprop)
requires ((p ** q) @==> r) ** p
ensures q @==> r
{
    elim_hyp_l _ _ _;
}
```

```pulse
ghost
fn test_elim_3 (p q r:vprop)
requires ((p ** q) @==> r) ** p ** q
ensures r
{
    elim (_ ** _) _;
}
```

```pulse
ghost
fn test_elim_3' (p q r:vprop)
requires ((p ** q) @==> r) ** p ** q
ensures r
{
    elim _ _; //unifier doesn't work when solving uvars to non-atomic vprops
}
```


```pulse
ghost fn test_elim_4 (p q r:vprop)
requires (p @==> (q ** r)) ** p
ensures r ** q
{ 
    elim _ _; //though it's fine when those solutions do not have to be matched again
}
```
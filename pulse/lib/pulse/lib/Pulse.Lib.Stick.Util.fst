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

module Pulse.Lib.Stick.Util
open Pulse.Lib.Pervasives
include Pulse.Lib.Stick

```pulse
ghost
fn intro
  (hyp concl: vprop)
  (v: vprop)
  (f_elim: (unit -> (
    stt_ghost unit emp_inames
    (v ** hyp)
    (fun _ -> concl)
  )))
requires v
ensures hyp @==> concl
{
    intro_stick _ _ _ f_elim;
    fold (hyp @==> concl);
}
```

```pulse
ghost
fn elim (p q:vprop)
   requires (p @==> q) ** p
   ensures q
{
  unfold (p @==> q);
  elim_stick p q;
}
```


```pulse
ghost
fn refl (p:vprop)
   requires emp
   ensures p @==> p
{
    ghost fn aux (u:unit)
    requires emp ** p
    ensures p
    { () };
    intro _ _ _ aux;
}
```

```pulse
ghost
fn curry (p q r:vprop)
   requires (p ** q) @==> r
   ensures p @==> (q @==> r)
{
    ghost fn aux (_:unit)
    requires ((p ** q) @==> r) ** p
    ensures q @==> r
    { 
        ghost fn aux (_:unit)
        requires (((p ** q) @==> r) ** p) ** q
        ensures r
        { 
            elim _ _;
        };
        intro _ _ _ aux;
    };
    intro _ _ _ aux;
}
```


```pulse
ghost
fn trans (p q r:vprop)
    requires (p @==> q) ** (q @==> r)
    ensures p @==> r
{
   ghost fn aux (_:unit)
   requires ((p @==> q) ** (q @==> r)) ** p
   ensures r
   { 
      elim _ _;
      elim _ _;
   };
   intro _ _ _ aux;
}
```

```pulse
ghost
fn comm_l (p q r:vprop)
   requires (p ** q) @==> r
   ensures (q ** p) @==> r
{
    ghost fn aux (_:unit)
    requires ((p ** q) @==> r) ** (q ** p)
    ensures r
    { 
        elim _ _;
    };
    intro _ _ _ aux;
}
```

```pulse
ghost
fn comm_r (p q r:vprop)
   requires p @==> (q ** r)
   ensures p @==> (r ** q)
{
    ghost fn aux (_:unit)
    requires (p @==> (q ** r)) ** p
    ensures r ** q
    { 
        elim _ _;
    };
    intro _ _ _ aux; 
}
```

```pulse
ghost
fn assoc_l (p q r s:vprop)
   requires (p ** (q ** r)) @==> s
   ensures ((p ** q) ** r) @==> s
{
    ghost fn aux (_:unit)
    requires ((p ** (q ** r)) @==> s) ** ((p ** q) ** r)
    ensures s
    { 
        elim _ _;
    };
    intro _ _ _ aux;
}
```

```pulse
ghost
fn assoc_r (p q r s:vprop)
   requires p @==> ((q ** r) ** s)
   ensures p @==> (q ** (r ** s))
{
    ghost fn aux (_:unit)
    requires (p @==> ((q ** r) ** s)) ** p
    ensures q ** (r ** s)
    { 
        elim _ _;
    };
    intro _ _ _ aux;
}
```

```pulse
ghost
fn elim_hyp_l (p q r:vprop)
    requires ((p ** q) @==> r) ** p
    ensures (q @==> r)
{
    curry _ _ _;
    elim _ _;
}
```

```pulse
ghost
fn elim_hyp_r (p q r:vprop)
    requires ((p ** q) @==> r) ** q
    ensures (p @==> r)
{
    comm_l _ _ _;
    curry _ _ _;
    elim _ _;
}
```

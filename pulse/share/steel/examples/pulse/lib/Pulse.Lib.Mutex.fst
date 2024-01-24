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

module Pulse.Lib.Mutex
open Pulse.Lib.Core

open Pulse.Lib.SpinLock
open Pulse.Lib.Box

open Pulse.Main

noeq
type mutex (#a:Type0) (p:a -> vprop) : Type0 = {
  r:box a;
  l:lock (exists* v. pts_to r v ** p v)
}

```pulse
fn new_mutex' (#a:Type0) (p:a -> vprop) (x:a)
  requires p x
  returns m:mutex p
  ensures emp
{
  let r = alloc x;
  let l = new_lock (exists* v. pts_to r v ** p v);
  let m = {r; l};
  m
}
```

let new_mutex = new_mutex'

let belongs_to_mutex (#a:Type0) (#p:a -> vprop) (r:box a) (m:mutex p) : vprop =
  pure (r == m.r)

```pulse
fn lock' (#a:Type0) (#p:a -> vprop) (m:mutex p)
  requires emp
  returns r:box a
  ensures r `belongs_to_mutex` m ** (exists* v. pts_to r v ** p v)
{
  acquire m.l;
  fold (belongs_to_mutex m.r m);
  m.r
} 
```

let lock = lock'

```pulse
fn unlock' (#a:Type0) (#p:a -> vprop) (m:mutex p) (r:box a)
  requires r `belongs_to_mutex` m ** (exists* v. pts_to r v ** p v)
  ensures emp
{
  unfold (belongs_to_mutex r m);
  with v. rewrite (pts_to r v) as (pts_to m.r v);
  release m.l;
}
```

let unlock = unlock'
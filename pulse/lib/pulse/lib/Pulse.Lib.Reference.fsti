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

module Pulse.Lib.Reference

open FStar.Tactics
open FStar.Ghost
open Pulse.Main
open Pulse.Lib.Core
open PulseCore.FractionalPermission

val ref ([@@@unused] a:Type u#0) : Type u#0

val pts_to
    (#a:Type)
    ([@@@equate_strict] r:ref a)
    (#[exact (`1.0R)] p:perm)
    (n:a)
  : vprop

val pts_to_is_small (#a:Type) (r:ref a) (p:perm) (x:a)
  : Lemma (is_small (pts_to r #p x))
          [SMTPat (is_small (pts_to r #p x))]

[@@deprecated "Reference.alloc is unsound; use Box.alloc instead"]
```pulse
val fn alloc
  (#a:Type)
  (x:a)
  requires emp
  returns  r : ref a
  ensures  pts_to r x
```

```pulse
(* ! *)
val fn op_Bang
  (#a:Type)
  (r:ref a)
  (#n:erased a)
  (#p:perm)
  requires pts_to r #p n
  returns  x : a
  ensures  pts_to r #p n ** pure (reveal n == x)
```

```pulse
(* := *)
val fn op_Colon_Equals
  (#a:Type)
  (r:ref a)
  (x:a)
  (#n:erased a)
  requires pts_to r n
  ensures  pts_to r x
```

[@@deprecated "Reference.free is unsound; use Box.free instead"]
```pulse
val fn free
  (#a:Type)
  (r:ref a)
  (#n:erased a)
  requires pts_to r n
  ensures  emp
```

```pulse
ghost
val fn share
  (#a:Type)
  (r:ref a)
  (#v:erased a)
  (#p:perm)
  requires pts_to r #p v
  ensures  pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
```

[@@allow_ambiguous]
```pulse
ghost
val fn gather
  (#a:Type)
  (r:ref a)
  (#x0 #x1:erased a)
  (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
```

(* Share/gather specialized to half permission *)
```pulse
ghost
val fn share2
  (#a:Type)
  (r:ref a)
  (#v:erased a)
  requires pts_to r v
  ensures  pts_to r #0.5R v ** pts_to r #0.5R v
```

[@@allow_ambiguous]
```pulse
ghost
val fn gather2
  (#a:Type)
  (r:ref a)
  (#x0 #x1:erased a)
  requires pts_to r #0.5R x0 ** pts_to r #0.5R x1
  ensures  pts_to r x0 ** pure (x0 == x1)
```

let cond b (p q:vprop) = if b then p else q

val with_local
  (#a:Type0)
  (init:a)
  (#pre:vprop)
  (#ret_t:Type)
  (#post:ret_t -> vprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                              (fun v -> post v ** op_exists_Star (pts_to r)))
  : stt ret_t pre post
(* NOTE: Pulse does not have  universe polymorphism yet,
(and ret_t is in a polymorphic universe), so we retain the val above.
The val fn below is what it would look like internally in Pulse, but we have to
fix a universe for ret_t. *)
// ```pulse
// val fn with_local
//   (#a:Type0)
//   (init:a)
//   (#pre:vprop)
//   (#ret_t:Type u#0)
//   (#post:ret_t -> vprop)
//   (body : (r:ref a) -> stt ret_t (pre ** pts_to r init)
//                                  (fun v -> post v ** op_exists_Star (pts_to r)))
//   requires pre
//   returns  v : ret_t
//   ensures  post v
// ```

[@@allow_ambiguous]
```pulse
ghost
val fn pts_to_injective_eq
  (#a:Type0)
  (#p #q:perm)
  (#v0 #v1:a)
  (r:ref a)
  requires pts_to r #p v0 ** pts_to r #q v1
  ensures  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)
```

```pulse
ghost
val fn pts_to_perm_bound
  (#a:Type0)
  (#p:perm)
  (r:ref a)
  (#v:a)
  requires pts_to r #p v
  ensures  pts_to r #p v ** pure (p <=. 1.0R)
```

```pulse
val fn replace
  (#a:Type0)
  (r:ref a)
  (x:a)
  (#v:erased a)
  requires pts_to r v
  returns  res : a
  ensures  pts_to r x ** pure (res == reveal v)
```

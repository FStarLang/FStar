(*
   Copyright 2024 Microsoft Research

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

module Example.StructPCM

open FStar.PCM
open Pulse.Lib.Core
open Pulse.Main

module G = FStar.Ghost
module PCM = FStar.PCM

//
// This example sketches a PCM for updating fields of a pair in parallel
//

type carrier (a:Type u#1) (b:Type u#1) : Type u#1 =
  | Unit
  | X : a -> carrier a b
  | Y : b -> carrier a b
  | XY : a -> b -> carrier a b

let one #a #b : carrier a b = Unit

let composable #a #b (v1 v2:carrier a b) : prop =
  match v1, v2 with
  | Unit, _
  | _, Unit
  | X _, Y _
  | Y _, X _ -> True
  | _ -> False

let op #a #b (v1:carrier a b) (v2:carrier a b { composable v1 v2 }) : carrier a b =
  match v1, v2 with
  | Unit, _ -> v2
  | _, Unit -> v1
  | X x, Y y
  | Y y, X x -> XY x y

let p #a #b : pcm' (carrier a b) = { composable; op; one }

let comm : lem_commutative p = fun _ _ -> ()
let assoc : lem_assoc_l p = fun _ _ _ -> ()
let assoc_r : lem_assoc_r p = fun _ _ _ -> ()
let is_unit : lem_is_unit p = fun _ -> ()
let refine #a #b : carrier a b -> prop = fun _ -> True

let spcm a b : pcm (carrier a b) = { p; comm; assoc; assoc_r; is_unit; refine }

let pcm_upd_x #a #b (x1 x2:a) : frame_preserving_upd (spcm a b) (G.hide (X x1)) (G.hide (X x2)) =
  function
  | Unit
  | X _ -> X x2
  | Y y
  | XY _ y -> XY x2 y

let pcm_upd_y #a #b (y1 y2:b) : frame_preserving_upd (spcm a b) (G.hide (Y y1)) (G.hide (Y y2)) =
  function
  | Unit
  | Y _ -> Y y2
  | X x
  | XY x _ -> XY x y2

let pcm_upd_xy #a #b (x1 x2:a) (y1 y2:b) : frame_preserving_upd (spcm a b) (G.hide (XY x1 y1)) (G.hide (XY x2 y2)) =
  fun _ -> XY x2 y2

type ref a b : Type0 = pcm_ref (spcm a b)

```pulse
fn alloc #a #b (x:a) (y:b)
  requires emp
  returns r:ref a b
  ensures pcm_pts_to r (XY x y)
{
  Pulse.Lib.Core.alloc #_ #(spcm a b) (XY x y)
}
```

```pulse
fn share #a #b (r:ref a b) (#x:a) (#y:b)
  requires pcm_pts_to r (XY x y)
  ensures pcm_pts_to r (X x) **
          pcm_pts_to r (Y y)
{
  rewrite pcm_pts_to r (XY x y) as
          pcm_pts_to r (X x `FStar.PCM.op (spcm a b)` Y y);
  Pulse.Lib.Core.share r (Ghost.hide (X x)) (Ghost.hide (Y y));
}
```

```pulse
fn upd_x #a #b (r:ref a b) (x1 x2:a)
  requires pcm_pts_to r (X x1)
  ensures pcm_pts_to r (X x2)
{
  Pulse.Lib.Core.write r _ _ (pcm_upd_x x1 x2)
}
```

```pulse
fn upd_y #a #b (r:ref a b) (y1 y2:b)
  requires pcm_pts_to r (Y y1)
  ensures pcm_pts_to r (Y y2)
{
  Pulse.Lib.Core.write r _ _ (pcm_upd_y y1 y2)
}
```

```pulse
fn upd #a #b (r:ref a b) (x1 x2:a) (y1 y2:b)
  requires pcm_pts_to r (XY x1 y1)
  ensures pcm_pts_to r (XY x2 y2)
{
  Pulse.Lib.Core.write r _ _ (pcm_upd_xy x1 x2 y1 y2)
}
```

```pulse
fn gather #a #b (r:ref a b) (#x:a) (#y:b)
  requires pcm_pts_to r (X x) **
           pcm_pts_to r (Y y)
  ensures pcm_pts_to r (XY x y)
{
  Pulse.Lib.Core.gather r (G.hide (X x)) (G.hide (Y y));
    rewrite pcm_pts_to r (X x `FStar.PCM.op (spcm a b)` Y y) as
            pcm_pts_to r (XY x y)

}
```

```pulse
fn upd_par #a #b (r:ref a b) (x1 x2:a) (y1 y2:b)
  requires pcm_pts_to r (XY x1 y1)
  ensures  pcm_pts_to r (XY x2 y2)
{
  share r;
  parallel
    requires pcm_pts_to r (X x1) and
             pcm_pts_to r (Y y1)
    ensures pcm_pts_to r (X x2) and
            pcm_pts_to r (Y y2)
    { upd_x r x1 x2 }
    { upd_y r y1 y2 };
  
  gather r
}
```

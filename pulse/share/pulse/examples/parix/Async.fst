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

module Async

open Pulse.Lib.Pervasives
open Pulse.Lib.Par.Pledge
open UnixFork

(* Pulse will currently not recognize calls to anything other than
top-level names, so this allows to force it. *)
val now
  (#a #pre #post : _)
  (f : unit -> stt a pre post)
  : unit -> stt a pre post
let now f () = f ()

let ref_solves_post (#a:Type0) (r:ref (option a)) (post : a -> vprop) : vprop =
  exists* (v:a). pts_to r (Some v) ** post v

(* NB: The vprop is not used here, so why the index? Only to make
it easier for users to call await, as the post should be unified
and hence the user would not need to explicitly repeat it. Unless
we can fill it from the context...? *)
let asynch (a:Type0) (post : a -> vprop) : Type0 =
  ref (option a) & thread

let async_joinable #a #post h =
  joinable (snd h) ** pledge emp_inames (done (snd h)) (ref_solves_post (fst h) post)

```pulse
fn async_fill
  (#a : Type0)
  (#pre : vprop)
  (#post : (a -> vprop))
  (f : (unit -> stt a pre (fun x -> post x)))
  (r : ref (option a))
  (_:unit)
  requires pre ** pts_to r None
  returns _ : unit
  ensures ref_solves_post r post
{
  // Very nice!
  let v : a = f ();
  r := Some v;
  fold ref_solves_post;
  ()
}
```

```pulse
fn __async
  (#a : Type0)
  (#pre : vprop)
  (#post : (a -> vprop))
  (f : (unit -> stt a pre post))
  requires pre
  returns h : asynch a post
  ensures async_joinable h
{
  let r = alloc (None #a);
  assume_ (pure (post == (fun x -> post x))); // Crucial for the call below to work, review
  let th = fork #(pre ** pts_to r None) #(ref_solves_post r post)
                (async_fill #a #pre #post f r);
  let res = ( r, th );
  
  assert (joinable th);
  assert (pledge emp_inames (done th) (ref_solves_post r post));
  rewrite (joinable th ** pledge emp_inames (done th) (ref_solves_post r post))
       as (async_joinable #_ #post res);
  res
}
```
let async = __async

```pulse
fn __await
  (#a : Type0)
  (#post : (a -> vprop))
  (h : asynch a post)
  requires async_joinable h
  returns x:a
  ensures post x
{
  let r = fst h;
  let th = snd h;
  unfold async_joinable;
  assert (joinable th);
  join th; (* join the thread *)
  assert (done th);
  rewrite (done th) as (done (snd h));
  redeem_pledge emp_inames (done (snd h)) (ref_solves_post r post);
  assert (ref_solves_post r post);
  unfold ref_solves_post;
  with vv. assert (pts_to r (Some vv));
  drop_ (done th);
  
  assert (post vv);
  assert (pts_to r (Some vv));

  let vo = !r;
  free r;
  match vo {
    Some v -> {
      rewrite (post vv) as (post v);
      assert (post v);
      v
    }
  }
}
```
let await = __await

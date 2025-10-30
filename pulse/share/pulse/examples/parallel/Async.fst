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
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Pledge
open UnixFork
module Box = Pulse.Lib.Box

let box_solves_post (#a:Type0) (r:Box.box (option a)) (post : a -> slprop) : slprop =
  exists* (v:a). Box.pts_to r (Some v) ** post v

(* NB: The slprop is not used here, so why the index? Only to make
it easier for users to call await, as the post should be unified
and hence the user would not need to explicitly repeat it. Unless
we can fill it from the context...? *)
let asynch (a:Type0) (post : a -> slprop) : Type0 =
  Box.box (option a) & thread

let async_joinable #a #post h =
  joinable (snd h) ** pledge emp_inames (done (snd h)) (box_solves_post (fst h) post)

(* Ugly, but at least it works fine. *)
let eta_post #a #b #pre #post (f : (x:a -> stt b (pre x) (post x)))
  : x:a -> stt b (pre x) (fun y -> post x y)
  = fun x ->
      sub_stt _ _
        (slprop_equiv_refl _)
        (intro_slprop_post_equiv _ _ (fun y -> slprop_equiv_refl _))
        (f x)


fn async_fill
  (#a : Type0)
  (#pre : slprop)
  (#post : (a -> slprop))
  (f : (unit -> stt a pre post))
  (r : Box.box (option a))
  (_:unit)
  requires pre ** Box.pts_to r None
  returns _ : unit
  ensures box_solves_post r post
{
  let f = eta_post f;
  // Very nice!
  let v : a = f ();
  Box.op_Colon_Equals r (Some v);
  fold (box_solves_post r post)
}



fn __async
  (#a : Type0)
  (#pre : slprop)
  (#post : (a -> slprop))
  (f : (unit -> stt a pre post))
  requires pre
  returns h : asynch a post
  ensures async_joinable h
{
  let r = Box.alloc (None #a);
  let th = fork #(pre ** Box.pts_to r None) #(box_solves_post r post)
                (async_fill #a #pre #post f r);
  let res = ( r, th );
  
  assert (joinable th);
  assert (pledge emp_inames (done th) (box_solves_post r post));
  rewrite (joinable th ** pledge emp_inames (done th) (box_solves_post r post))
       as (async_joinable #_ #post res);
  res
}

let async = __async


fn __await
  (#a : Type0)
  (#post : (a -> slprop))
  (h : asynch a post)
  requires async_joinable h
  returns x:a
  ensures post x
{
  let r = fst h;
  let th = snd h;
  unfold async_joinable;
  rewrite each fst h as r;
  rewrite each snd h as th;
  assert (joinable th);
  join th; (* join the thread *)
  assert (done th);
  redeem_pledge emp_inames (done th) (box_solves_post r post);
  assert (box_solves_post r post);
  unfold box_solves_post;
  with vv. assert (Box.pts_to r (Some vv));
  drop_ (done th);
  
  assert (post vv);
  assert (Box.pts_to r (Some vv));

  let vo = Box.op_Bang r;
  Box.free r;
  match vo {
    Some v -> {
      rewrite (post vv) as (post v);
      assert (post v);
      v
    }
  }
}

let await = __await


fn __map
  (#a : Type0)
  (#b : Type0)
  (#post1 : (a -> slprop))
  (#post2 : (b -> slprop))
  (f : (x:a -> stt b (post1 x) post2))
  (h : asynch a post1)
  requires async_joinable h
  returns  h' : asynch b post2
  ensures  async_joinable h'
{
  let r' = Box.alloc (None #b);
  fn filler (_:unit)
    requires async_joinable h ** Box.pts_to r' None
    ensures box_solves_post r' post2
  {
    let x = await h;
    let f = eta_post f;
    let y : b = f x;
    Box.op_Colon_Equals r' (Some y);
    fold (box_solves_post r' post2)
  };
  let waiter = fork filler;
  let h' : asynch b post2 = (r', waiter);
  rewrite each r' as (fst h');
  rewrite each waiter as (snd h');
  fold (async_joinable h');
  h'
}

let map = __map

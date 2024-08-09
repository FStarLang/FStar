(*
   Copyright 2008-2018 Microsoft Research

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
module Shallow

open SepLogic.Heap

module S = FStar.Squash

let memory = m:memory{defined m}

(* postcondition, a predicate on the return value and the output heap *)
let post (a:Type) = a * heap -> Type0

(* precondition, a predicate on the input heap *)
let pre = heap -> Type0

(* wp *)
let st_wp (a:Type) = post a -> pre

(* result type parametrized by a post *)
let result (h0:heap) (a:Type) (post:post a) = 
  x_h:(a * heap){post x_h /\ fresh_or_old h0 (snd #a #heap x_h)}

(* st computation, also parametrized by a post *)
let st (a:Type) (wp:st_wp a) = 
  post:post a -> h0:heap{wp post h0} -> Tot (squash (result h0 a post))

(* return *)
let return_without_binding (#a:Type) (x:a)
  : st a (fun post h0 -> heap_memory h0 == emp /\ post (x, h0))
  = fun post h0 -> S.return_squash (x, h0)

let return_with_binding (#a:Type) (x:a)
  : st a (fun post h0 -> post (x, h0))
  = fun post h0 -> S.return_squash (x, h0)

(* frame wp by partitioning a heap whose memory is m into h0 and h1, and then prove post on the resulting heap and h1 *)
let frame_wp0 (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h:heap) (m0 m1:memory) =
  defined (m0 <*> m1) /\ 
  heap_memory h == (m0 <*> m1) /\ 
  (let (h0,h1) = split_heap m0 m1 h in wp (post h1) h0)

let frame_wp1 (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h:heap) (m0:memory) =
  exists m1. frame_wp0 wp post h m0 m1

let frame_wp (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h:heap) =
  exists m0. frame_wp1 wp post h m0

(* the idea is to call frame_wp with (frame_post p)? yes, see frame below *)
let frame_post (#a:Type) (p:post a) (h0:heap) : post a =
  fun x_h1 -> 
    let (x, h1) = x_h1 in 
    defined (heap_memory h0 <*> heap_memory h1) /\ p (x, join h0 h1)

let bind_exists
  (#a:Type)
  (#b:Type)
  (#p:b -> Type)
  (h:(exists (x:b). p x))
  (f:(x:b -> p x -> Tot (squash a)))
  : Tot (squash a)
  = S.bind_squash #(x:b & p x) #a h (fun (| x, p |) -> f x p)

val frame: #a:Type -> #wp:st_wp a -> f:st a wp
         -> st a (fun post -> frame_wp wp (frame_post post))
let frame #a #wp f = 
  fun post h -> 
    assert (frame_wp wp (frame_post post) h); 
    let s = S.join_squash (S.get_proof (frame_wp wp (frame_post post) h)) in 
    bind_exists #(result h a post) #memory #(frame_wp1 wp (frame_post post) h) s (fun m0 s' -> 
      assert (frame_wp1 wp (frame_post post) h m0); 
      bind_exists #(result h a post) #memory #(frame_wp0 wp (frame_post post) h m0) s' (fun m1 _ -> 
        assert (frame_wp0 wp (frame_post post) h m0 m1); 
        let (h0,h1) = split_heap m0 m1 h in 
        let sqres : squash (result h0 a (frame_post post h1)) = f (frame_post post h1) h0 in 
        S.bind_squash #(result h0 a (frame_post post h1))
                      #(result h a post)
                      sqres
                      (fun (x_h0':result h0 a (frame_post post h1)) -> 
                         let (x, h0') = x_h0' in
                         let res = (x, join h1 h0') in 
                         lemma_fresh_or_old_disjoint h0 h0' h1;
                         lemma_fresh_or_old_sep h0 h0' h1;
                         lemma_join_comm h0' h1;
                         S.return_squash res)))

#set-options "--z3rlimit_factor 1 --max_fuel 0 --max_ifuel 0"

val bind_without_framing (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h0 -> wp1 (fun (x, h1) -> wp2 x post h1) h0)
let bind_without_framing #a #wp1 #b #wp2 f g = 
  fun post h0 -> 
    let sq_1 : squash (result h0 a (fun (x, h1) -> wp2 x post h1)) =
      f (fun (x,h1) -> wp2 x post h1) h0 in
    S.bind_squash sq_1 (fun (x,h1) -> 
      let sq_2 : squash (x_h:(b * heap){post x_h /\ fresh_or_old h1 (snd x_h)}) =
        g x post h1 in 
        S.bind_squash sq_2 (fun (y,h2) -> 
          assert (fresh_or_old h0 h2);
          let sq_3 : squash (x_h:(b * heap){post x_h /\ fresh_or_old h0 (snd x_h)}) = 
            S.return_squash (y,h2) in
          sq_3))
        
val bind_with_framing (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h ->
            frame_wp wp1 (frame_post (fun (x, h1) ->
              frame_wp (wp2 x) (frame_post post) h1)) h)

let bind_with_framing #a #wp1 #b #wp2 f g =
    fun post h0 ->
      let sq_1 : squash (result h0 a (fun (x, h1) -> frame_wp (wp2 x) (frame_post post) h1)) =
        frame f (fun (x, h1) -> frame_wp (wp2 x) (frame_post post) h1) h0 in
      S.bind_squash sq_1 (fun (x, h1) ->
        let sq_2 : squash (x_h:(b * heap){post x_h /\ fresh_or_old h1 (snd x_h)}) =
          frame (g x) post h1 in 
        S.bind_squash sq_2 (fun (y,h2) -> 
          assert (fresh_or_old h0 h2);
          let sq_3 : squash (x_h:(b * heap){post x_h /\ fresh_or_old h0 (snd x_h)}) = 
            S.return_squash (y,h2) in
          sq_3))

let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post h0 -> exists (x:a). heap_memory h0 == (r |> x) /\ post (x, h0))

let read_without_framing (#a:Type0) (r:ref a)
  : st a (read_wp r)
  = fun post h0 -> 
      assert_norm (read_wp r post h0 
                   ==> 
                   (exists (x:a). heap_memory h0 == (r |> x) /\ post (x, h0)));
      assert (mcontains (heap_memory h0) r);
      S.return_squash (sel h0 r, h0)

let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
   fun post h0 -> 
     frame_wp (read_wp r) (frame_post post) h0

let read_with_framing (#a:Type0) (r:ref a)
  : st a (frame_read_wp r)
  = fun post h0 -> 
      frame (read_without_framing r) post h0

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  fun post h0 -> 
    exists (x:a). (heap_memory h0 == (r |> x) /\ post ((), (upd h0 r v)))

let write_without_framing (#a:Type0) (r:ref a) (v:a)
  : st unit (write_wp r v)
    = fun post h0 -> 
        assert_norm (write_wp r v post h0 
                     ==> 
                     (exists (x:a). heap_memory h0 == (r |> x) /\ post ((), upd h0 r v)));
        lemma_fresh_or_old_upd r v h0;
        S.return_squash ((), upd h0 r v)

let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
   fun post h0 -> 
     frame_wp (write_wp r v) (frame_post post) h0

let write_with_framing (#a:Type0) (r:ref a) (v:a)
  : st unit (frame_write_wp r v)
  = fun post h0 -> 
      frame (write_without_framing r v) post h0

let alloc_wp (#a:Type0) (x:a) : st_wp (ref a)
  = fun post h0 -> 
      heap_memory h0 == emp /\ post (alloc h0 x)

let alloc_without_framing (#a:Type0) (x:a)
  : st (ref a) (alloc_wp x)
  = fun post h0 ->
      let (r,h1) = alloc h0 x in
      lemma_fresh_or_old_alloc x h0;
      S.return_squash (r,h1)

let frame_alloc_wp (#a:Type0) (x:a) : st_wp (ref a) =
  fun post h0 ->
    frame_wp (alloc_wp x) (frame_post post) h0

let alloc_with_framing (#a:Type0) (x:a)
  : st (ref a) (frame_alloc_wp x)
  = fun post h0 -> 
      frame (alloc_without_framing x) post h0

let dealloc_wp (#a:Type0) (r:ref a) : st_wp unit = 
  fun post h0 -> 
    (exists x . heap_memory h0 == (r |> x) /\ post ((), dealloc h0 r))

let dealloc_without_framing (#a:Type0) (r:ref a)
  : st unit (dealloc_wp r)
  = fun post h0 -> 
        assert_norm (dealloc_wp r post h0 
                     ==> 
                     (exists x . heap_memory h0 == (r |> x) /\ post ((), dealloc h0 r)));
        let h1 = dealloc h0 r in
        lemma_fresh_or_old_dealloc r h0;
        S.return_squash ((), h1)
        
let frame_dealloc_wp (#a:Type0) (r:ref a) : st_wp unit = 
  fun post h0 -> 
    frame_wp (dealloc_wp r) (frame_post post) h0

let dealloc_with_framing (#a:Type0) (r:ref a)
  : st unit (frame_dealloc_wp r)
  = fun post h0 -> 
      frame (dealloc_without_framing r) post h0

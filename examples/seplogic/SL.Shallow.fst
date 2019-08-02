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
module SL.Shallow

open SL.Heap

module S = FStar.Squash

unfold let memory = m:memory{defined m}

(* postcondition, a predicate on the return value and the output heap *)
let post (a:Type) = a * memory -> Type0

(* precondition, a predicate on the input heap *)
let pre = memory -> Type0

(* wp *)
let st_wp (a:Type) = post a -> pre

(* result type parametrized by a post *)
let result (a:Type) (post:post a) = x:(a * heap){post (fst x, heap_memory (snd x))}

(* st computation, also parametrized by a post *)
let st (a:Type) (wp:st_wp a) = 
  post:post a -> h0:heap{wp post (heap_memory h0)} -> Tot (squash (result a post))

(* return *)
let return (#a:Type) (x:a)
  : st a (fun post m0 -> m0 == emp /\ post (x, m0))
  = fun post h0 -> S.return_squash (x, h0)

(* frame wp by partitioning a heap whose memory is m into h0 and h1, and then prove post on the resulting heap and h1 *)
let frame_wp0 (#a:Type) (wp:st_wp a) (post:memory -> (a * memory) -> Type0) (m m0 m1:memory) =
  defined (m0 <*> m1) /\ m == (m0 <*> m1) /\ wp (post m1) m0

let frame_wp1 (#a:Type) (wp:st_wp a) (post:memory -> (a * memory) -> Type0) (m m0:memory) =
  exists (m1:memory). frame_wp0 wp post m m0 m1

let frame_wp (#a:Type) (wp:st_wp a) (post:memory -> (a * memory) -> Type0) (m:memory) =
  exists (m0:memory). frame_wp1 wp post m m0

(* the idea is to call frame_wp with (frame_post p)? yes, see frame below *)
let frame_post (#a:Type) (p:post a) (m0:memory) ((x, m1):(a * memory)) = 
  defined (m0 <*> m1) /\ p (x, m0 <*> m1)

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
//Expanded out:
//         st a (fun post m -> exists m0 m1. disjoint m0 m1 /\ m == m0 <*> m1 /\ wp (fun m0' -> disjoint m0' m1 /\ post (x, (join_tot h0' h1))) m0
let frame #a #wp f = 
  fun post h ->
    assert (frame_wp wp (frame_post post) (heap_memory h));
    let s = S.join_squash (S.get_proof (frame_wp wp (frame_post post) (heap_memory h))) in
    bind_exists #(result a post) #memory #(frame_wp1 wp (frame_post post) (heap_memory h)) s (fun m0 s' -> 
      assert (frame_wp1 wp (frame_post post) (heap_memory h) m0);
      bind_exists #(result a post) #memory #(frame_wp0 wp (frame_post post) (heap_memory h) m0) s' (fun m1 _ -> 
        assert (frame_wp0 wp (frame_post post) (heap_memory h) m0 m1);
        let (h0,h1) = split_heap m0 m1 h in
        let sqres : squash (result a (frame_post post (heap_memory h1))) = f (frame_post post (heap_memory h1)) h0 in 
        S.bind_squash #(result a (frame_post post (heap_memory h1)))
                      #(result a post)
                      sqres
                      (fun (x_h0':result a (frame_post post (heap_memory h1))) -> 
                         let (x, h0') = x_h0' in
                         let res = (x, join h1 h0') in 
                         S.return_squash res)))

val bind_without_framing (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post m0 ->
              wp1 (fun (x,m1) -> wp2 x post m1) m0)
let bind_without_framing #a #wp1 #b #wp2 f g =
    fun post h0 ->
      let sq_1 : squash (result a (fun (x,m1) -> wp2 x post m1)) =
        f (fun (x,m1) -> wp2 x post m1) h0 in
      S.bind_squash sq_1 (fun (x, m1) ->
        g x post m1)

val bind_with_framing (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h ->
            frame_wp wp1 (frame_post (fun (x, h1) ->
              frame_wp (wp2 x) (frame_post post) h1)) h)
let bind_with_framing #a #wp1 #b #wp2 f g =
    fun post h0 ->
      let sq_1 : squash (result a (fun (x,m1) -> frame_wp (wp2 x) (frame_post post) m1)) =
        frame f (fun (x,m1) -> frame_wp (wp2 x) (frame_post post) m1) h0 in
      S.bind_squash sq_1 (fun (x, m1) ->
        frame (g x) post m1)

let read_wp (#a:Type) (r:ref a) : st_wp a =
    (fun post m0 -> exists (x:a). m0 == (r |> x) /\ post (x, m0))

let frame_read_wp (#a:Type) (r:ref a) : st_wp a =
   fun post h0 -> 
     frame_wp (read_wp r) (frame_post post) h0

let read_without_framing (#a:Type0) (r:ref a)
  : st a (read_wp r)
  = fun post h0 -> 
      assert_norm (read_wp r post (heap_memory h0) 
                   ==> 
                   (exists (x:a). heap_memory h0 == (r |> x) /\ post (x, heap_memory h0)));
      assert (mcontains (heap_memory h0) r);
      S.return_squash (sel h0 r, h0)

let read_with_framing (#a:Type0) (r:ref a)
  : st a (frame_read_wp r)
  = fun post h0 -> 
      frame (read_without_framing r) post h0

let write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
  fun post m0 -> 
    exists (x:a). (m0 == (r |> x) /\ post ((), (r |> v)))

let frame_write_wp (#a:Type) (r:ref a) (v:a) : st_wp unit =
   fun post m0 -> 
     frame_wp (write_wp r v) (frame_post post) m0

let write_without_framing (#a:Type0) (r:ref a) (v:a)
  : st unit (write_wp r v)
    = fun post h0 -> 
        assert_norm (write_wp r v post (heap_memory h0) 
                     ==> 
                     (exists (x:a). heap_memory h0 == (r |> x) /\ post ((), (r |> v))));
        assert (mcontains (heap_memory h0) r);
        S.return_squash ((), upd h0 r v)

let write_with_framing (#a:Type0) (r:ref a) (v:a)
  : st unit (frame_write_wp r v)
  = fun post h0 -> 
      frame (write_without_framing r v) post h0

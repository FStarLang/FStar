module Shallow

open SepLogic.Heap

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
  post:post a -> h0:heap{wp post (heap_memory h0)} -> GTot (squash (result a post))

(* return *)
let return (#a:Type) (x:a)
  : st a (fun post m0 -> m0 == emp /\ post (x, m0))
  = fun post h0 -> FStar.Squash.return_squash (x, h0)

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

module S = FStar.Squash

let bind_exists
  (#a:Type)
  (#b:Type)
  (#p:b -> Type)
  (h:(exists (x:b). p x))
  (f:(x:b -> p x -> GTot (squash a)))
  : GTot (squash a)
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
        assert (disjoint_heaps h0 h1);
        let sqres : squash (result a (frame_post post (heap_memory h1))) = f (frame_post post (heap_memory h1)) h0 in 
        S.bind_squash #(result a (frame_post post (heap_memory h1)))
                      #(result a post)
                      sqres
                      (fun (x_h0':result a (frame_post post (heap_memory h1))) -> 
                         let (x, h0') = x_h0' in
                         let res = (x, join h1 h0') in 
                         S.return_squash res)))
      
val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post m ->
            frame_wp wp1 (frame_post (fun (x, m1) ->
              frame_wp (wp2 x) (frame_post post) m1)) m)
let bind #a #wp1 #b #wp2 f g =
    fun post h ->
      let sq_1 : squash (result a (fun (x, m1) -> frame_wp (wp2 x) (frame_post post) m1)) =
        frame f (fun (x, m1) -> frame_wp (wp2 x) (frame_post post) m1) h in
      S.bind_squash sq_1 (fun (x, m1) ->
      frame (g x) post m1)

let alloc (#a:Type0) (x:a)
  : st (ref a) (fun post m0 -> m0 == emp /\ (forall r m1 . m1 == (r |> x) ==> post (r, m1)))
  = fun post h0 ->
      let (r,h1) = alloc h0 x in
      S.return_squash (r,h1)

let read (#a:Type0) (r:ref a)
  : st a (fun post m0 -> (exists (x:a). m0 == (r |> x) /\ post (x, m0)))
  = fun post h0 -> 
      assert (mcontains (heap_memory h0) r);
      S.return_squash (sel h0 r, h0)

let write (#a:Type0) (r:ref a) (v:a)
  : st unit (fun post m0 -> (exists (x:a). m0 == (r |> x) /\ post ((), (r |> v))))
    = fun post h0 -> 
        assert (mcontains (heap_memory h0) r);
        S.return_squash ((), upd h0 r v)

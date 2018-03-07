module Shallow

open SepLogic.Heap

(* postcondition, a predicate on the return value and the output heap *)
let post (a:Type) = a * heap -> Type0

(* precondition, a predicate on the input heap *)
let pre = heap -> Type0

(* wp *)
let st_wp (a:Type) = post a -> pre

(* result type parametrized by a post *)
let result (a:Type) (post:post a) = x:(a * heap){post x}

(* st computation, also parametrized by a post *)
let st (a:Type) (wp:st_wp a) = post:post a -> h0:heap{wp post h0} -> GTot (squash (result a post))

(* return *)
let return (#a:Type) (x:a)
  : st a (fun post h0 -> emp h0 /\ post (x, h0))
  = fun post h0 -> FStar.Squash.return_squash (x, h0)

(* frame wp by partitioning h into h0 and h1, and then prove post on the resulting heap and h1 *)
let frame_wp0 (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h h0 h1:heap) =
  disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ wp (post h1) h0

(* frame_wp1 and frame_wp2 existentially quantify over h0 and h1 *)
let frame_wp1 (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h h0:heap) =
  exists (h1:heap). frame_wp0 wp post h h0 h1

let frame_wp (#a:Type) (wp:st_wp a) (post:heap -> (a * heap) -> Type0) (h:heap) =
  (* expanded out:
   * exists (h0:heap) (h1:heap). disjoint h0 h1 /\ h == join_tot h0 h1 /\ wp (post h1) h0
   *)
  exists (h0:heap). frame_wp1 wp post h h0

(* the idea is to call frame_wp with (frame_post p)? yes, see frame below *)
let frame_post (#a:Type) (p:post a) (h:heap) ((x, h1):(a * heap)) = p (x, join_tot h h1)

module S = FStar.Squash
let bind_exists
  (#a:Type)
  (#b:Type)
  (#p:b -> Type)
  (h:(exists (x:b). p x))
  (f:(x:b -> p x -> GTot (squash a)))
  : GTot (squash a)
  = Squash.bind_squash #(x:b & p x) #a h (fun (| x, p |) -> f x p)

val frame: #a:Type -> #wp:st_wp a -> f:st a wp
         -> st a (fun post -> frame_wp wp (frame_post post))
//Expanded out:
//         st a (fun post h -> exists h0 h1. disjoint h0 h1 /\ h == join_tot h0 h1 /\ wp (fun h0' -> post (x, (join_tot h0' h1))) h0
let frame #a #wp f =
  fun post h ->
    assert (frame_wp wp (frame_post post) h);  //from the refinement annotation on st type
    let s = FStar.Squash.join_squash (FStar.Squash.get_proof (frame_wp wp (frame_post post) h)) in
    bind_exists #(result a post) #heap #(frame_wp1 wp (frame_post post) h) s (fun h0 s' ->
      assert (frame_wp1 wp (frame_post post) h h0);
      bind_exists #(result a post) #heap #(frame_wp0 wp (frame_post post) h h0) s' (fun h1 _ ->
        assert (frame_wp0 wp (frame_post post) h h0 h1);
        //so now, h0 and h1 are the frames
        let sqres : squash (result a (frame_post post h1)) = f (frame_post post h1) h0 in
        S.bind_squash #(result a (frame_post post h1))
                      #(result a post)
                      sqres (fun (x_h0':result a (frame_post post h1)) ->
          let x, h0' = x_h0' in
          let res = x, join_tot h1 h0' in  //AR: had to change the order of h1 and h0', joint_tot commutativity lemma?
          FStar.Squash.return_squash res)))

val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h ->
            frame_wp wp1 (frame_post (fun (x, h1) ->
              frame_wp (wp2 x) (frame_post post) h1)) h)
let bind #a #wp1 #b #wp2 f g =
    fun post h ->
      let sq_1 : squash (result a (fun (x, h1) -> frame_wp (wp2 x) (frame_post post) h1)) =
        frame f (fun (x, h1) -> frame_wp (wp2 x) (frame_post post) h1) h in
      S.bind_squash sq_1 (fun (x, h1) ->
      frame (g x) post h1)

let read (#a:Type) (r:ref a)
  : st a (fun post h0 -> (exists (x:a). (r |> x) h0 /\ post (x, h0)))
  = fun post h0 -> FStar.Squash.return_squash (sel_tot h0 r, h0)

let write (#a:Type) (r:ref a) (v:a)
  : st unit (fun post h0 -> (exists (x:a). (r |> x) h0 /\ (forall h1. (r |> v) h1 ==> post ((), h1))))
    = fun post h0 -> FStar.Squash.return_squash ((), upd_tot h0 r v)

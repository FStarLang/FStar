module Shallow
open FStar.SL.Heap

let post a = a * heap -> Type0
let pre = heap -> Type0
let st_wp (a:Type) = post a -> pre
let result (a:Type) post = x:(a * heap){ post x }
let st (a:Type) (wp:st_wp a) =
    post:post a ->
    h0:heap{wp post h0} ->
    GTot (squash (result a post))

let return (#a:Type) (x:a)
    : st a (fun post h0 -> is_emp h0 /\ post (x, h0))
    = fun post h0 -> FStar.Squash.return_squash (x, h0)

let frame_wp0 #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h h0 h1 =
        h == join_tot h0 h1 /\ wp (post h1) h0

let frame_wp1 #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h h0 =
    exists (h1:heap). frame_wp0 wp post h h0 h1

let frame_wp #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h =
    exists (h0:heap). frame_wp1 wp post h h0

let frame_post #a (p:post a) (h:heap) (x, h1) = p (x, join_tot h h1)

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
//         st a (fun post h -> exists h0 h1. h == join_tot h0 h1 /\ wp (fun h0' -> post (x, (join_tot h0' h1))) h0
let frame #a #wp f =
  fun post h ->
    assert (frame_wp wp (frame_post post) h);
    let s = FStar.Squash.join_squash (FStar.Squash.get_proof (frame_wp wp (frame_post post) h)) in
    bind_exists #(result a post) #heap #(frame_wp1 wp (frame_post post) h) s (fun h0 s' ->
    assert (frame_wp1 wp (frame_post post) h h0);
    bind_exists #(result a post) #heap #(frame_wp0 wp (frame_post post) h h0) s' (fun h1 _ ->
    assert (frame_wp0 wp (frame_post post) h h0 h1);
    let sqres : squash (result a (frame_post post h1)) = f (frame_post post h1) h0 in
    S.bind_squash #(result a (frame_post post h1))
                  #(result a post)
                  sqres (fun (x_h0':result a (frame_post post h1)) ->
    let x, h0' = x_h0' in
    let res = x, join_tot h0' h1 in
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

assume
val points_to_contains (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (points_to r x `contains` r))
          [SMTPat (points_to r x)]

assume
val points_to_sel (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (sel_tot (points_to r x) r == x))
          [SMTPat (sel_tot (points_to r x) r)]

assume
val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a)
  : Lemma (ensures (upd_tot (points_to r x) r v == points_to r v))
          [SMTPat (upd_tot (points_to r x) r v)]

let read (#a:Type) (r:ref a)
    : st a (fun post h0 ->
                   (exists (x:a). h0 == points_to r x)
                 /\ (forall x. h0 == points_to r x ==> post (x, h0)))
    = fun post h0 -> FStar.Squash.return_squash (sel_tot h0 r, h0)

let write (#a:Type) (r:ref a) (v:a)
    : st unit (fun post h0 ->
                   (exists (x:a). h0 == points_to r x)
                 /\ post ((), points_to r v))
    = fun post h0 -> FStar.Squash.return_squash ((), upd_tot h0 r v)

let swap (r:ref int) (s:ref int) =
  x <-- read r ;
  y <-- read s ;
  write r y  ;;
  write s x

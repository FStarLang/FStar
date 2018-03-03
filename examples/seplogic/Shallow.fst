module Shallow
open FStar.SL.Heap


let st_wp (a:Type0) = (a * heap -> Type0) -> heap -> Type0
let st (a:Type0) (wp:st_wp a) =
    post:(a * heap -> Type0) ->
    h0:heap{wp post h0} ->
    GTot (squash (x:(a * heap){post x}))
                      
                    // (fun post -> wp post h0)

let return (#a:Type) (x:a) 
    : st a (fun post h0 -> is_emp h0 /\ post (x, h0))
    = fun post h0 -> FStar.Squash.return_squash (x, h0)

let split0 h h0 h1 = h == join_tot h0 h1
let split1 h h0 = exists (h1:heap). split0 h h0 h1
let split h = exists (h0:heap). split1 h h0

let frame_wp0 #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h h0 h1 = 
        h == join_tot h0 h1 /\ wp (post h1) h0

let frame_wp1 #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h h0 = 
    exists (h1:heap). frame_wp0 wp post h h0 h1

let frame_wp #a (wp:st_wp a) (post:heap -> (a * heap) -> Type0) h = 
    exists (h0:heap). frame_wp1 wp post h h0

let bind_wp2 #a #b (wp2: a -> st_wp b) post frame_h (x, h1) =
        frame_wp (wp2 x) (fun frame_h1 (y, h2) ->
          post (y, join_tot h2 frame_h1))
        (join_tot h1 frame_h)

val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g: (x:a -> st b (wp2 x)))
    : st b (fun post h ->
      frame_wp wp1 (fun frame_h (x, h1) ->
        frame_wp (wp2 x) (fun frame_h1 (y, h2) ->
          post (y, join_tot h2 frame_h1))
        (join_tot h1 frame_h))
      h)
      
module S = FStar.Squash
let bind_exists
     (#a:Type)
     (#b:Type)
     (#p:b -> Type)
     (h:(exists (x:b). p x))
     (f:(x:b -> p x -> GTot (squash a)))
     : GTot (squash a)
     = Squash.bind_squash #(x:b & p x) #a h (fun (| x, p |) -> f x p)
 
let bind_split
    (#a:Type)
    (h:heap{split h})
    (f: (h0:heap -> h1:heap{h == join_tot h0 h1} -> GTot (squash a)))
    : GTot (squash a)
    = let s = FStar.Squash.join_squash (FStar.Squash.get_proof (split h)) in
      bind_exists #a #heap #(split1 h) s (fun (h0:heap) (s1:split1 h h0) ->
      bind_exists #a #heap #(split0 h h0) s1 (fun (h1:heap) (s0:split0 h h0 h1) ->
      f h0 h1))
let post a = a * heap -> Type0

let result (a:Type) post = (x:(a * heap){ post x })
let weaken (#a:Type) (h:heap) (post:heap -> post a) (x:squash (result a (post h))) :
    squash (result a (fun x -> exists h. post h x)) =
    S.bind_squash x (fun (res:(a * heap) {post h res}) ->
    assert (exists h. post h res);
    let res' :result a (fun res -> exists h. post h res) = res in
    S.return_squash res')
    
let bind_frame
    (a:Type0)
    (wp:st_wp a)
    (post:heap -> post a)
    (h:heap{frame_wp wp post h})
    (f: (h0:heap -> h1:heap{frame_wp0 wp post h h0 h1} -> GTot (squash (result a (post h1)))))
    : GTot (squash (result a (fun x -> exists h1. post h1 x)))
    = let s = FStar.Squash.join_squash (FStar.Squash.get_proof (frame_wp wp post h)) in
      bind_exists #(result a (fun x -> exists h1. post h1 x)) 
                  #heap
                  #(frame_wp1 wp post h)
                  s 
                  (fun (h0:heap) (s1:frame_wp1 wp post h h0) ->
      bind_exists #(x:(a * heap){ exists h1. post h1 x })
                  #heap 
                  #(frame_wp0 wp post h h0) 
                  s1 (fun (h1:heap) (s0:frame_wp0 wp post h h0 h1) ->
      weaken h1 post (f h0 h1)))

let frame_post #a (p:post a) (h:heap) (x, h1) = p (x, join_tot h h1)
val frame: #a:Type -> #wp:st_wp a -> f:st a wp
         -> st a (fun post -> frame_wp wp (frame_post post))
let elim_squash_result #a #post (x:squash (result a post)) : squash (x:(a * heap){post x}) = 
  let y : (x:unit{result a post}) = x in
  y
let intro_squash_result #a #post (x:squash (x:(a * heap){post x})) : squash (result a post) =
  let y : (x:unit{result a post}) = x in
  y
let frame #a #wp f =
  fun post h ->
    assert (frame_wp wp (frame_post post) h);
    bind_frame a wp (frame_post post) h (fun h0 h1 -> 
    intro_squash_result #a #(frame_post post h1) (f (frame_post post h1) h0))
    
        

#set-options "--max_fuel 0 --max_ifuel 1 --initial_ifuel 1 --z3rlimit 20"
let bind #a #wp1 #b #wp2 f g =
  fun post h -> 
     bind_frame a wp1 (bind_wp2 wp2 post) h (fun h1 frame_h ->
     let squash_ah1 = f (bind_wp2 wp2 post frame_h) h1 in
     admit();
     magic())

//implementing this is tricky, since there isn't a direct way to
//compute the split of h3 into h2' and h2''
//it suggests that we might use a slightly difference style of spec

assume 
val points_to_contains (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (points_to r x `contains` r))
          [SMTPat (points_to r x)]

assume
val points_to_sel (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (sel_tot (points_to r x) r == x))
          [SMTPat (sel_tot (points_to r x) r)]

let read (#a:Type) (r:ref a)
    : st a (fun post h0 ->
                   (exists (x:a). h0 == points_to r x)
                 /\ (forall x. h0 == points_to r x ==> post (x, h0)))
    = fun post h0 -> FStar.Squash.return_squash (sel_tot h0 r, h0)

assume
val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a)
  : Lemma (ensures (upd_tot (points_to r x) r v == points_to r v))
          [SMTPat (upd_tot (points_to r x) r v)]

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
  




// // assume 
// // val read : #a:Type 
// //          -> r:ref a
// //          -> ST a

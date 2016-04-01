module FStar.All
assume new type heap : Type0
let all_pre = all_pre_h heap
let all_post (a:Type) = all_post_h heap a
let all_wp (a:Type) = all_wp_h heap a
new_effect ALL = ALL_h heap
effect All (a:Type) (pre:all_pre) (post: (heap -> Tot (all_post a))) =
       ALL a
           (fun (p:all_post a) (h:heap) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* WP  *)
           (fun (p:all_post a) (h:heap) -> forall ra h1. (pre h /\ post h ra h1) ==> p ra h1) (* WLP *)
effect ML (a:Type) =
  ALL a (all_null_wp heap a) (all_null_wp heap a)

inline let lift_exn_all (a:Type) (wp:ex_wp a)   (p:all_post a) (h:heap) = wp (fun ra -> p ra h)
sub_effect EXN   ~> ALL = lift_exn_all

assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val failwith: string -> 'a
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a


module All
type heap
kind AllPre = AllPre_h heap
kind AllPost (a:Type) = AllPost_h heap a
kind AllWP (a:Type) = AllWP_h heap a
new_effect ALL = ALL_h heap
effect All (a:Type) (pre:AllPre) (post: (heap -> AllPost a)) =
       ALL a
           (fun (p:AllPost a) (h:heap) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* AllWP *)
           (fun (p:AllPost a) (h:heap) -> forall ra h1. (pre h /\ post h ra h1) ==> p ra h1) (* WLP *)
default effect ML (a:Type) =
  ALL a (all_null_wp heap a) (all_null_wp heap a)
sub_effect
  EXN   ~> ALL = fun (a:Type) (wp:ExWP a)   (p:AllPost a) (h:heap) -> wp (fun ra -> p ra h)

assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val failwith: string -> 'a
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a

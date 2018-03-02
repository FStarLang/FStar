module PartitionedShallow

open FStar.SL.Heap

let st_wp (a:Type0) = (a * heap -> Type0) -> heap -> Type0

unfold let sep_wp (a:Type0) (wp:st_wp a) (post:(a * heap -> Type0)) (h0:heap) = 
  (exists h0' h0'' . disjoint h0' h0'' /\ h0 == join_tot h0' h0'' /\ 
                     wp (fun (x,h1) -> disjoint h1 h0'' /\ post (x,join_tot h1 h0'')) h0')

(*unfold let sep_wp (a:Type0) (wp:st_wp a) (post:(a * heap -> Type0)) (h0:heap) = 
  (exists h0' h0'' . h0 == join_tot h0' h0'' /\ wp (fun (x,h1) -> post (x,join_tot h1 h0'')) h0')*)

let st (a:Type0) (wp:st_wp a) =
    h0:heap -> PURE (a * heap) (fun post -> sep_wp a wp post h0)
                        

(* ******* *)

let return (#a:Type) (x:a) 
    : st a (fun post' h0' -> is_emp h0' /\ post' (x,h0'))
    = fun h0 -> x,h0

(* ******* *)

//TODO: Assumed because currently bind cannot be implemented even 
//      for standard shallow embedding of st (and even for pure).
//      Also, see the note on the right about its soundness.

assume
val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g:(x:a -> st b (wp2 x)))
    : st b (fun post' h0' -> wp1 (fun (x,h1) -> wp2 x post' h1) h0')      //<-- NOTE: In order to type the standard definition of bind 
//    = fun h0 -> let (x,h1) = f h0 in g x h1                             //          against the given WP, we would need to remove the
                                                                          //          disjointness conditions from sep_wp (see paper note).
                                                                          //
                                                                          //          But then it is not guaranteed that the given reference 
                                                                          //          r is actually contained in the initial heap of the 
                                                                          //          read and write actions below because one might have
                                                                          //
                                                                          //          h0 == join_tot (points_to r x) h0''
                                                                          //          ==>
                                                                          //          h0 == emp
                                                                          //
                                                                          //          if, for example, one takes h0'' = (points_to r y)

(* ******* *)

assume 
val lemma_points_to_contains (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (points_to r x `contains` r))
          [SMTPat (points_to r x)]

assume
val lemma_points_to_sel (#a:Type) (r:ref a) (x:a)
  : Lemma (ensures (sel_tot (points_to r x) r == x))
          [SMTPat (sel_tot (points_to r x) r)]

assume
val lemma_contains_disjoint (#a:Type) (r:ref a) (h0:heap) (h1:heap)
  : Lemma (requires (disjoint h0 h1 /\ contains h0 r))
          (ensures  (contains (join_tot h0 h1) r))
          [SMTPat (contains (join_tot h0 h1) r)]

assume 
val lemma_sel_disjoint (#a:Type0) (r:ref a) (h0:heap) (h1:heap)
  : Lemma (requires (disjoint h0 h1 /\ contains h0 r))
          (ensures  (sel_tot (join_tot h0 h1) r == sel_tot h0 r))
          [SMTPat (sel_tot #a (join_tot h0 h1) r)]

let lemma_read (#a:Type0) (r:ref a) (post:(a * heap -> Type0)) (h0:heap) (h0':heap) (h0'':heap)
  : Lemma (requires (disjoint h0' h0'' /\ h0 == join_tot h0' h0'' /\ (exists x . h0' == points_to r x /\ post (x,join_tot h0' h0''))))
          (ensures  (contains h0 r /\ post (sel_tot h0 r, h0)))
          [SMTPat (post (sel_tot h0 r, h0)); SMTPat (disjoint h0' h0'')]
  = ()

let read (#a:Type0) (r:ref a)
    : st a (fun post' h0' -> exists x . h0' == points_to r x /\ post' (x,h0'))
    = fun h0 -> sel_tot h0 r, h0                                                //<-- need disjointness in sep_wp to establish (contains h0 r)

(* ******* *)

assume
val lemma_points_to_upd (#a:Type0) (r:ref a) (x:a) (v:a)
  : Lemma (ensures (upd_tot (points_to r x) r v == points_to r v))
          [SMTPat (upd_tot (points_to r x) r v)]

assume
val lemma_disjoint_points_to (#a:Type0) (r:ref a) (v:a) (w:a) (h:heap)
  : Lemma (requires (disjoint (points_to r v) h))
          (ensures  (disjoint (points_to r w) h))
          [SMTPat (disjoint (points_to r v) h); SMTPat (disjoint (points_to r w) h)]
          
assume
val lemma_upd_tot_points_to (#a:Type0) (r:ref a) (v:a) (w:a) (h:heap)
  : Lemma (requires (disjoint (points_to r v) h))
          (ensures  (upd_tot (join_tot (points_to r v) h) r w ==  join_tot (points_to r w) h))
          [SMTPat (upd_tot (join_tot (points_to r v) h) r w); SMTPat (join_tot (points_to r w) h)]

let lemma_write (#a:Type0) (r:ref a) (v:a) (post:(unit * heap -> Type0)) (h0:heap) (h0':heap) (h0'':heap)
  : Lemma (requires (disjoint h0' h0'' /\ h0 == join_tot h0' h0'' /\ (exists (x:a). h0' == points_to r x) /\ post ((), join_tot (points_to r v) h0'')))
          (ensures  (post ((), upd_tot h0 r v)))
          [SMTPat (post ((), upd_tot h0 r v)); SMTPat (disjoint h0' h0'')]
  = ()

let write (#a:Type0) (r:ref a) (v:a)
    : st unit (fun post' h0' -> (exists (x:a). h0' == points_to r x) /\ post' ((), points_to r v))
    = fun h0 -> (), upd_tot h0 r v                                                                  //<-- need disjointness in sep_wp to establish (contains h0 r)


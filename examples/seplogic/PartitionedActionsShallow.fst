module PartitionedActionsShallow

open FStar.SL.Heap

let st_wp (a:Type0) = (a * heap -> Type0) -> heap -> Type0

let st (a:Type0) (wp:st_wp a) =
    h0:heap -> PURE (a * heap) (fun post -> wp post h0)    

(* Return *)

let return (#a:Type) (x:a) 
    : st a (fun post h0 -> post (x,h0))
    = fun h0 -> x,h0

(* Bind *)

assume
val bind (#a:Type) (#wp1:st_wp a)
         (#b:Type) (#wp2:a -> st_wp b)
         (f:st a wp1)
         (g:(x:a -> st b (wp2 x)))
    : st b (fun post h0 -> wp1 (fun (x,h1) -> wp2 x post h1) h0)

(* Alloc *)

let alloc (#a:Type0) (v:a)
    : st (ref a) (fun post h0 -> post (alloc (trivial_preorder a) h0 v false))
    = fun h0 -> alloc (trivial_preorder a) h0 v false

(* Read *)

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

let read (#a:Type0) (r:ref a)
    : st a (fun post h0 -> exists h0' x . disjoint (points_to r x) h0' /\ h0 == join_tot (points_to r x) h0' /\ post (x,h0))
    = fun h0 -> sel_tot h0 r, h0

(* Write *)

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

let write (#a:Type0) (r:ref a) (v:a)
    : st unit (fun post h0 -> exists h0' x . disjoint (points_to r x) h0' /\ h0 == join_tot (points_to r x) h0' /\ post ((), join_tot (points_to r v) h0'))
    = fun h0 -> (), upd_tot h0 r v

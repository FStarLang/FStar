module SepLogic.Heap

module S  = FStar.Set
module TS = FStar.TSet

let set  = Set.set
let tset = TSet.set

val heap :Type u#1

let hpred = heap -> Type0

val ref (a:Type0) :Type0

val addr_of: #a:Type0 -> ref a -> GTot nat

val join_tot: h1:heap -> h2:heap -> Tot heap

val disjoint : #a:Type -> #b:Type -> ref a -> ref b -> Type0
val disjoint_heaps : heap -> heap -> Type0

val emp : hpred
val ( |> ) : #a:Type0 -> r:ref a -> x:a -> hpred
val ( <*> ) : hpred -> hpred -> hpred

val sep_interp (p q:hpred) (h:heap)
    : Lemma ((p <*> q) h <==> (exists h0 h1. disjoint_heaps h0 h1 /\ h == join_tot h0 h1 /\ p h0 /\ q h1))

val emp_unit  (p:hpred) (h:heap) 
    : Lemma ((p <*> emp) h <==> p h)

val sep_comm (p q:hpred) (h:heap)
    : Lemma ((p <*> q) h <==> (q <*> p) h)

val sep_assoc (p q r:hpred) (h:heap)
    : Lemma ((p <*> (q <*> r)) h <==> ((p <*> q) <*> r) h)

val fresh : #a:Type -> ref a -> hpred
val contains : #a:Type -> heap -> ref a -> Type0

val points_to_contains (#a:Type) (r:ref a) (x:a) (h:heap)
  : Lemma (requires (r |> x) h)
          (ensures  (h `contains` r))
          [SMTPat ((r |> x) h);
           SMTPat (h `contains` r)]

val points_to_disj (#a:Type) (#b:Type) (r:ref a) (s:ref b) (x:a) (y:b) (h:heap)
    : Lemma (requires (r |> x <*> s |> y) h)
            (ensures  (disjoint r s))

val sel_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot a
val upd_tot: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> x:a -> Tot heap

val points_to_sel (#a:Type) (r:ref a) (x:a) (h:heap)
  : Lemma (requires (r |> x) h)
          (ensures  (sel_tot h r == x))
          [SMTPat ((r |> x) h);
           SMTPat (sel_tot h r)]

val points_to_upd (#a:Type) (r:ref a) (x:a) (v:a) (h:heap)
  : Lemma  (requires (r |> x) h)
           (ensures  ((r |> v) (upd_tot h r v)))
           [SMTPat ((r |> x) h);
            SMTPat (upd_tot h r v)]

val restrict: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot heap
val minus: #a:Type0 -> h:heap -> r:ref a{h `contains` r} -> Tot heap

val minus_contains (#a:Type0) (r:ref a) (h:heap)
  : Lemma (requires (h `contains` r))
          (ensures  (~((h `minus` r) `contains` r)))

val restrict_points_to (#a:Type0) (r:ref a) (h:heap)
  : Lemma (requires (h `contains` r))
          (ensures  (exists x . (r |> x) (restrict h r)))

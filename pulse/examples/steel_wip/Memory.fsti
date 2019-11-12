module Memory
open FStar.Real
let perm =
  r:FStar.Real.real{
    FStar.Real.(0.0R <. r && r <=. 1.0R)
  }

val mem  : Type u#1
val ref (a:Type u#0) : Type u#0

val disjoint (m0 m1:mem) : prop
val join (m0:mem) (m1:mem{disjoint m0 m1}) : mem

val hprop : Type u#1
val pts_to (#a:_) (r:ref a) (p:perm) (v:a) : hprop
val h_and (p1 p2:hprop) : hprop
val h_or  (p1 p2:hprop) : hprop
val star  (p1 p2:hprop) : hprop
val wand  (p1 p2:hprop) : hprop
val h_exists (#a:Type0) (f: (a -> hprop)) : hprop
val h_forall (#a:Type0) (f: (a -> hprop)) : hprop

let ptr_perm #a (r:ref a) (p:perm) =
    h_exists (fun v -> pts_to r p v)

let ptr #a (r:ref a) =
    h_exists (fun p -> ptr_perm r p)

val interp (p:hprop) (m:mem) : prop
let hmem (p:hprop) = m:mem{interp p m}
let equiv (p1 p2:hprop) =
  forall m. interp p1 m <==> interp p2 m

val star_commutative (p1 p2:hprop)
  : Lemma ((p1 `star` p2) `equiv` (p2 `star` p1))
val star_associative (p1 p2 p3:hprop)
  : Lemma ((p1 `star` (p2 `star` p3))
           `equiv`
           ((p1 `star` p2) `star` p3))

val sel (#a:_) (r:ref a) (m:hmem (ptr r))
  : a

val sel_lemma (#a:_) (r:ref a) (p:perm) (m:hmem (ptr_perm r p))
  : Lemma (interp (ptr r) m /\
           interp (pts_to r p (sel r m)) m)

val split_mem (p1 p2:hprop) (m:hmem (p1 `star` p2))
  : Tot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})

val upd (#a:_) (r:ref a) (v:a)
        (frame:hprop)
        (m:hmem (ptr_perm r 1.0R  `star` frame))
  : Tot (m:hmem (pts_to r 1.0R v `star` frame))

val intro_wand (p1 p2:hprop) (m:mem)
  : Lemma
    (requires
      (forall (m0:hmem p1).
         disjoint m0 m /\
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)

val elim_wand (p1 p2:hprop) (m:mem)
  : Lemma
    (requires
      (interp ((p1 `wand` p2) `star` p1) m))
    (ensures
      interp p2 m)

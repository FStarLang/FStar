(*--build-config
options:--admit_fsi FStar.Set;
other-files: set.fsi;
--*)
module FStar.Heap
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
open FStar.Set
type heap
type ref : Type -> Type
type aref =
  | Ref : #a:Type -> r:ref a -> aref
assume logic val sel :       #a:Type -> heap -> ref a -> Tot a
assume logic val upd :       #a:Type -> heap -> ref a -> a -> Tot heap
assume logic val emp :       heap
assume logic val contains :  #a:Type -> heap -> ref a -> Tot bool
assume logic val equal:      heap -> heap -> Tot bool
assume logic val restrict:   heap -> set aref -> Tot heap
assume logic val concat:     heap -> heap -> Tot heap

assume SelUpd1:       forall (a:Type) (h:heap) (r:ref a) (v:a).            {:pattern (sel (upd h r v) r)}
                      sel (upd h r v) r == v

assume SelUpd2:       forall (a:Type) (b:Type) (h:heap) (k1:ref a) (k2:ref b) (v:b).{:pattern (sel (upd h k2 v) k1)}
                      k2=!=k1 ==> sel (upd h k2 v) k1 == sel h k1

assume ContainsUpd:   forall (a:Type) (b:Type) (h:heap) (k1:ref a) (k2:ref b) (v:a).{:pattern contains (upd h k1 v) k2}
                      contains (upd h k1 v) k2 <==> (k1==k2 \/ contains h k2)

assume InDomEmp:      forall (a:Type) (k:ref a).                           {:pattern contains emp k}
                      not(contains emp k)

assume Extensional:   forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> h1 == h2

assume Equals:        forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> (forall (a:Type) (k:ref a).{:pattern (sel h1 k); (sel h2 k)} sel h1 k == sel h2 k)

assume RestrictSel:   forall (a:Type) (h:heap) (r:set aref) (a:ref a).     {:pattern sel (restrict h r) a}
                      mem (Ref a) r ==> sel (restrict h r) a == sel h a

assume RestrictIn:    forall (a:Type) (h:heap) (r:set aref) (a:ref a).     {:pattern contains (restrict h r) a}
                      contains (restrict h r) a == (mem (Ref a) r && contains h a)

assume SelConcat:     forall (a:Type) (h1:heap) (h2:heap) (a:ref a).       {:pattern sel (concat h1 h2) a}
                      if b2t (contains h2 a) then sel (concat h1 h2) a==sel h2 a else sel (concat h1 h2) a == sel h1 a

assume ContainsConcat:forall (a:Type) (h1:heap) (h2:heap) (a:ref a).       {:pattern contains (concat h1 h2) a}
                      contains (concat h1 h2) a == (contains h1 a || contains h2 a)

type On (r:set aref) (p:(heap -> Type)) (h:heap) = p (restrict h r)
opaque type fresh (refs:set aref) (h0:heap) (h1:heap) =
  (forall (a:Type) (a:ref a).{:pattern (contains h0 a)} mem (Ref a) refs ==> not(contains h0 a) /\ contains h1 a)
opaque logic type modifies (mods:set Heap.aref) (h:heap) (h':heap) =
    b2t (equal h' (concat h' (restrict h (complement mods))))

let only x = Set.singleton (Ref x)

val op_Hat_Plus_Plus : #a:Type -> r:ref a -> set aref -> Tot (set aref)
let op_Hat_Plus_Plus (#a:Type) r s = Set.union (Set.singleton (Ref r)) s

val op_Plus_Plus_Hat : #a:Type -> set aref -> r:ref a -> Tot (set aref)
let op_Plus_Plus_Hat (#a:Type) s r = Set.union s (Set.singleton (Ref r))

val op_Hat_Plus_Hat : #a:Type -> #b:Type -> ref a -> ref b -> Tot (set aref)
let op_Hat_Plus_Hat (#a:Type) (#b:Type) r1 r2 = Set.union (Set.singleton (Ref r1)) (Set.singleton (Ref r2))

(*--build-config
    options:--admit_fsi FStar.List --admit_fsi FStar.Set;
    other-files:set.fsi ext.fst ghost.fst FStar.Regions.Located.fst
  --*)

module FStar.Regions.Heap

(** A series of lemmas about the heap and our lref type. *)
open FStar.Regions.Located
open FStar.Ghost
open FStar.Set
type ref : Type -> Type 
type lref (a:Type) : Type = located (ref a)

assume type heapAux
type heap = erased heapAux
//TODO
//Would be good to make heap polymorphic in the reference type
//so that we can just derive this by instantiation

type aref =
  | Ref : #a:Type -> r:lref a -> aref
//TODO make all these functions GTot; note heap is already erased
assume val sel :       #a:Type -> heap -> lref a -> Tot (*erased*) a
assume val upd :       #a:Type -> heap -> lref a -> a -> Tot heap
assume val emp :       heap
assume val contains :  #a:Type -> heap -> lref a -> Tot (*erased*) bool
assume val equal:      heap -> heap -> Tot (*erased*) bool
assume val restrict:   heap -> set aref -> Tot heap
assume val concat:     heap -> heap -> Tot heap

assume SelUpd1:       forall (a:Type) (h:heap) (r:lref a) (v:a).            {:pattern (sel (upd h r v) r)}
                      sel (upd h r v) r == v

assume SelUpd2:       forall (a:Type) (b:Type) (h:heap) (k1:lref a) (k2:lref b) (v:b).{:pattern (sel (upd h k2 v) k1)}
                      k2=!=k1 ==> sel (upd h k2 v) k1 == sel h k1

assume ContainsUpd:   forall (a:Type) (b:Type) (h:heap) (k1:lref a) (k2:lref b) (v:a).{:pattern contains (upd h k1 v) k2}
                      contains (upd h k1 v) k2 <==> (k1==k2 \/ contains h k2)

assume InDomEmp:      forall (a:Type) (k:lref a).                           {:pattern contains emp k}
                      not(contains emp k)

assume Extensional:   forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> h1 == h2

assume Equals:        forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> (forall (a:Type) (k:lref a).{:pattern (sel h1 k); (sel h2 k)} sel h1 k == sel h2 k)

assume RestrictSel:   forall (a:Type) (h:heap) (r:set aref) (a:lref a).     {:pattern sel (restrict h r) a}
                      mem (Ref a) r ==> sel (restrict h r) a == sel h a

assume RestrictIn:    forall (a:Type) (h:heap) (r:set aref) (a:lref a).     {:pattern contains (restrict h r) a}
                      contains (restrict h r) a == (mem (Ref a) r && contains h a)

assume SelConcat:     forall (a:Type) (h1:heap) (h2:heap) (a:lref a).       {:pattern sel (concat h1 h2) a}
                      if b2t (contains h2 a) then sel (concat h1 h2) a==sel h2 a else sel (concat h1 h2) a == sel h1 a

assume ContainsConcat:forall (a:Type) (h1:heap) (h2:heap) (a:lref a).       {:pattern contains (concat h1 h2) a}
                      contains (concat h1 h2) a == (contains h1 a || contains h2 a)

type On (r:set aref) (p:(heap -> Type)) (h:heap) = p (restrict h r)
opaque type fresh (lrefs:set aref) (h0:heap) (h1:heap) =
  (forall (a:Type) (a:lref a).{:pattern (contains h0 a)} mem (Ref a) lrefs ==> not(contains h0 a) /\ contains h1 a)
opaque type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (equal h' (concat h' (restrict h (complement mods))))

type modset = erased (set aref)

val only : #a:Type -> lref a -> Tot modset
let only x = hide (Set.singleton (Ref x))

val eonly : #a:Type -> erased (lref a) -> Tot modset
let eonly r = (elift1 (fun x -> (Set.singleton (Ref x)))) r

val eunion : s1:modset -> s2:modset -> Tot modset
let eunion s1 s2 = (elift2 union) s1 s2

val eunionUnion : #a:Type  -> #b:Type  -> r1:lref a -> r2:lref b ->
  Lemma (requires True) (ensures ((eunion (only r1) (only r2)) = hide (union (singleton (Ref r1)) (singleton (Ref r2)))))
  (* [SMTPat (eunion (only r1) (only r2))] *)
let eunionUnion r1 r2 = ()

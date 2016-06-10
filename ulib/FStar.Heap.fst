module FStar.Heap
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
open FStar.Set
assume new type heap : Type0
abstract type ref (a:Type) = 
  | MkRef of a //this implementation of ref is not realistic; it's just to get the universes right
#reset-options
noeq type aref =
  | Ref : #a:Type -> r:ref a -> aref
assume val sel :       #a:Type -> heap -> ref a -> Tot a
assume val upd :       #a:Type -> heap -> ref a -> a -> Tot heap
assume val emp :       heap
assume val contains :  #a:Type -> heap -> ref a -> Tot bool
assume val equal:      heap -> heap -> Tot bool
assume val restrict:   heap -> set aref -> Tot heap
assume val concat:     heap -> heap -> Tot heap
assume val domain:     heap -> Tot (set aref)

assume SelUpd1:       forall (a:Type) (h:heap) (r:ref a) (v:a).            {:pattern (sel (upd h r v) r)}
                      sel (upd h r v) r == v

assume SelUpd2:       forall (a:Type) (b:Type) (h:heap) (k1:ref a) (k2:ref b) (v:b).{:pattern (sel (upd h k2 v) k1)}
                      k2=!=k1 ==> sel (upd h k2 v) k1 == sel h k1

assume InDomEmp:      forall (a:Type) (k:ref a).                           {:pattern contains emp k}
                      not(contains emp k)

assume Extensional:   forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> h1 == h2

assume Equals:        forall (h1:heap) (h2:heap).                          {:pattern equal h1 h2}
                      equal h1 h2 <==> (forall (a:Type) (k:ref a).          {:pattern (sel h1 k); (sel h2 k)} sel h1 k == sel h2 k)

assume RestrictSel:   forall (a:Type) (h:heap) (r:set aref) (a:ref a).     {:pattern sel (restrict h r) a}
                      mem (Ref a) r ==> sel (restrict h r) a == sel h a

assume SelConcat:     forall (a:Type) (h1:heap) (h2:heap) (a:ref a).       {:pattern sel (concat h1 h2) a}
                      if contains h2 a then sel (concat h1 h2) a==sel h2 a else sel (concat h1 h2) a==sel h1 a

assume DomUpd:        forall (a:Type) (h:heap) (k1:ref a) (v:a).           {:pattern domain (upd h k1 v)}
                      domain (upd h k1 v) = Set.union (domain h) (Set.singleton (Ref k1))

assume DomRestrict:   forall (h:heap) (r:set aref).                        {:pattern domain (restrict h r)}
                      domain (restrict h r) == Set.intersect (domain h) r

assume DomConcat:     forall (h1:heap) (h2:heap).                          {:pattern domain (concat h1 h2)}
                      domain (concat h1 h2)  == Set.union (domain h1) (domain h2)

assume DomEmp:        domain emp = Set.empty

assume DomContains:   forall (a:Type) (h:heap) (r:ref a).                  {:pattern contains h r}
	              contains h r <==> Set.mem (Ref r) (domain h)

type on (r:set aref) (p:(heap -> Type)) (h:heap) = p (restrict h r)
type fresh (refs:set aref) (h0:heap) (h1:heap) =
  (forall (a:Type) (a:ref a).{:pattern (contains h0 a)} mem (Ref a) refs ==> not(contains h0 a) /\ contains h1 a)
type modifies (mods:set aref) (h:heap) (h':heap) =
    equal h' (concat h' (restrict h (complement mods)))
    /\ Set.subset (domain h) (domain h')

abstract val lemma_modifies_trans: m1:heap -> m2:heap -> m3:heap
                       -> s1:Set.set aref -> s2:Set.set aref
                       -> Lemma (requires (modifies s1 m1 m2 /\ modifies s2 m2 m3))
                               (ensures (modifies (Set.union s1 s2) m1 m3))
let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

let only x = Set.singleton (Ref x)

(* val op_Hat_Plus_Plus<u> : #a:Type(u) -> r:ref a -> set (aref<u>) -> Tot (set (aref<u>)) *)
let op_Hat_Plus_Plus (#a:Type) r s = Set.union (Set.singleton (Ref r)) s

(* val op_Plus_Plus_Hat<u> : #a:Type(u) -> set (aref<u>) -> r:ref a -> Tot (set (aref<u>)) *)
let op_Plus_Plus_Hat (#a:Type) s r = Set.union s (Set.singleton (Ref r))

(* val op_Hat_Plus_Hat<u> : #a:Type(u) -> #b:Type(u) -> ref a -> ref b -> Tot (set (aref<u>)) *)
let op_Hat_Plus_Hat (#a:Type) (#b:Type) r1 r2 = Set.union (Set.singleton (Ref r1)) (Set.singleton (Ref r2))

module Set
open Prims.PURE
assume type set : Type -> Type

assume val empty:      a:Type -> Tot (set a)
assume val singleton : a:Type -> a -> Tot (set a)
assume val union     : a:Type -> set a -> set a -> Tot (set a)
assume val intersect : a:Type -> set a -> set a -> Tot (set a)
assume val complement: a:Type -> set a -> Tot (set a)
assume val mem:        a:Type -> a -> set a -> Tot bool
assume val equal:      a:Type -> set a -> set a -> Tot bool

assume MemEmpty:      forall (key:Type) (k:key).                           {:pattern mem k empty}
                      not (mem k empty)

assume MemSingleton:  forall (key:Type) (k:key) (k':key).                  {:pattern mem k (singleton k')}
                      mem k (singleton k') == (k=k')

assume MemUnion:      forall (key:Type) (s1:set key) (s2:set key) (k:key). {:pattern mem k (union s1 s2)}
                      mem k (union s1 s2) == (mem k s1 || mem k s2)

assume MemIntersect:  forall (key:Type) (s1:set key) (s2:set key) (k:key). {:pattern mem k (intersect s1 s2)}
                      mem k (intersect s1 s2) == (mem k s1 && mem k s2)

assume MemComplement: forall (key:Type) (s1:set key) (k:key).              {:pattern mem k (complement s1)}
                      mem k (complement s1) == not(mem k s1)

assume Extensional:   forall (key:Type) (s1:set key) (s2:set key).         {:pattern (equal s1 s2)}              
                      equal s1 s2 <==> s1 == s2

assume Equals:        forall (key:Type) (s1:set key) (s2:set key).         {:pattern (equal s1 s2)}              
                      equal s1 s2 <==> (forall k.{:pattern (mem k s1); (mem k s2)} mem k s1 == mem k s2)

(* derived forms *)
let minus      (a:Type) (s1:set a) (s2:set a)  = intersect s1 (complement s2)

opaque type Subset' (a:Type) (s1:set a) (s2:set a) = 
       (forall (x:a).{:pattern mem x s1} mem x s1 ==> mem x s2)


type Subset : #a:Type -> set a -> set a -> Type = 
    fun (a:Type) (s1:set a) (s2:set a) -> Subset' a s1 s2

module Map
open Prims.PURE
open Set

assume type t : Type -> Type -> Type
assume logic val sel :       key:Type -> value:Type -> t key value -> key -> Tot value
assume logic val upd :       key:Type -> value:Type -> t key value -> key -> value -> Tot (t key value)
assume logic val const :     key:Type -> value:Type -> v:value -> Tot (t key value)
assume logic val concat:     key:Type -> value:Type -> t key value -> t key value -> Tot (t key value)
assume logic val contains:   key:Type -> value:Type -> t key value -> key -> Tot bool
assume logic val equal:      key:Type -> value:Type -> t key value -> t key value -> Tot bool
assume logic val restrict:   key:Type -> value:Type -> set key -> t key value -> Tot (t key value)

assume SelUpd1:       forall (key:Type) (value:Type) (m:t key value) (k:key) (v:value).          {:pattern sel (upd m k v) k}
                      sel (upd m k v) k == v

assume SelUpd2:       forall (key:Type) (value:Type) (m:t key value) (k1:key) (k2:key) (v:value).{:pattern sel (upd m k2 v) k1}
                      k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1

assume SelConst:      forall (key:Type) (value:Type) (v:value) (k:key).                          {:pattern sel (const v) k}
                      sel (const v) k == v

assume SelRestrict:   forall (key:Type) (value:Type) (m:t key value) (ks:set key) (k:key).       {:pattern sel (restrict ks m) k}
                      mem k ks ==> sel (restrict ks m) k == sel m k

assume SelConcat1:    forall (key:Type) (value:Type) (m1:t key value) (m2:t key value) (k:key).  {:pattern sel (concat m1 m2) k}
                      contains m2 k ==> sel (concat m1 m2) k==sel m2 k

assume SelConcat1:    forall (key:Type) (value:Type) (m1:t key value) (m2:t key value) (k:key).  {:pattern sel (concat m1 m2) k}
                      not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k

assume InDomUpd1:     forall (key:Type) (value:Type) (m:t key value) (k1:key) (k2:key) (v:value).   {:pattern contains (upd m k1 v) k2}
                      contains (upd m k1 v) k2 == (k1=k2 || contains m k2)

assume InDomUpd2:     forall (key:Type) (value:Type) (m:t key value) (k1:key) (k2:key) (v:value).{:pattern contains (upd m k2 v) k1}
                      k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1

assume InDomConstMap: forall (key:Type) (value:Type) (v:value) (k:key).                          {:pattern contains (const v) k}
                      contains (const v) k

assume InDomConcat:   forall (key:Type) (value:Type) (m1:t key value) (m2:t key value) (k:key).  {:pattern contains (concat m1 m2) k}
                      contains (concat m1 m2) k==(contains m1 k || contains m2 k)

assume InDomRestrict: forall (key:Type) (value:Type) (m:t key value) (ks:set key) (k:key).       {:pattern contains (restrict ks m) k}
                      contains (restrict ks m) k == mem k ks

assume ContainsConst: forall (key:Type) (value:Type) (v:value) (k:key).                          {:pattern contains (const v) k}
                      not (contains (const v) k)

assume Extensional:   forall (key:Type) (value:Type) (m1:t key value) (m2:t key value).          {:pattern (equal m1 m2)}
                      equal m1 m2 <==> m1 == m2

assume Equals:        forall (key:Type) (value:Type) (m1:t key value) (m2:t key value).          {:pattern (equal m1 m2)}
                      equal m1 m2 <==> (forall k.{:pattern (sel m1 k); (sel m2 k)} sel m1 k == sel m2 k)

let const_on (key:Type) (value:Type) (dom:set key) (v:value) = restrict dom (const v)

opaque type DisjointDom (key:Type) (value:Type) (m1:t key value) (m2:t key value) =
          (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))


module Heap
open Set

type aref = 
  | Ref : a:Type -> r:ref a -> aref

type refs =
  | AllRefs : refs
  | SomeRefs : v:set aref -> refs

let no_refs  = SomeRefs empty
let a_ref  r = SomeRefs (singleton (Ref r))

assume logic val sel :       a:Type -> heap -> ref a -> Tot a
assume logic val upd :       a:Type -> heap -> ref a -> a -> Tot heap
assume logic val emp :       heap
assume logic val contains :  a:Type -> heap -> ref a -> Tot bool
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
opaque type fresh (h:heap) (refs:set aref)       = (forall (a:Type) (a:ref a).{:pattern (contains h a)} mem (Ref a) refs ==> not(contains h a))

  

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

assume Extensional:   forall (key:Type) (value:Type) (m1:t key value) (m2:t key value).          {:pattern (equal m1 m2)}
                      equal m1 m2 <==> m1 == m2

assume Equals:        forall (key:Type) (value:Type) (m1:t key value) (m2:t key value).          {:pattern (equal m1 m2)}
                      equal m1 m2 <==> (forall k.{:pattern (sel m1 k); (sel m2 k)} sel m1 k == sel m2 k)

let const_on (key:Type) (value:Type) (dom:set key) (v:value) = restrict dom (const v)

opaque type DisjointDom (key:Type) (value:Type) (m1:t key value) (m2:t key value) =
          (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

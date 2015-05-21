module Map
open Prims.PURE
open Set

type t : Type -> Type -> Type

val sel: #key:Type -> #value:Type -> t key value -> key -> Tot value
val upd: #key:Type -> #value:Type -> t key value -> key -> value -> Tot (t key value)
val const: #key:Type -> #value:Type -> value -> Tot (t key value)
val concat: #key:Type -> #value:Type -> t key value -> t key value -> Tot (t key value)
val contains: #key:Type -> #value:Type -> t key value -> key -> Tot bool
val restrict: #key:Type -> #value:Type -> set key -> t key value -> Tot (t key value)

val lemma_SelUpd1: #key:Type -> #value:Type -> m:t key value -> k:key -> v:value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k = v))
		   [SMTPat (sel (upd m k v) k)]

val lemma_SelUpd2: #key:Type -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 = sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

val lemma_SelConst: #key:Type -> #value:Type -> v:value -> k:key ->
                    Lemma (requires True) (ensures (sel (const v) k == v))
                    [SMTPat (sel (const v) k)]

val lemma_SelRestrict: #key:Type -> #value:Type -> m:t key value -> ks:set key -> k:key ->
                       Lemma (requires True) (ensures (mem k ks ==> sel (restrict ks m) k == sel m k))
                       [SMTPat (sel (restrict ks m) k)]

val lemma_SelConcat1: #key:Type -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (contains m2 k ==> sel (concat m1 m2) k==sel m2 k))
                      [SMTPat (sel (concat m1 m2) k)]

val lemma_SelConcat2: #key:Type -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k))
                      [SMTPat (sel (concat m1 m2) k)]

val lemma_InDomUpd1: #key:Type -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

val lemma_InDomUpd2: #key:Type -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
                     [SMTPat (contains (upd m k2 v) k1)]

val lemma_InDomConstMap: #key:Type -> #value:Type -> v:value -> k:key ->
                         Lemma (requires True) (ensures (contains (const v) k))
                         [SMTPat (contains (const v) k)]

val lemma_InDomConcat: #key:Type -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                 Lemma (requires True) (ensures (contains (concat m1 m2) k==(contains m1 k || contains m2 k)))
                 [SMTPat (contains (concat m1 m2) k)]

val lemma_InDomRestrict: #key:Type -> #value:Type -> m:t key value -> ks:set key -> k:key ->
                         Lemma (requires True) (ensures (contains (restrict ks m) k == mem k ks))
                         [SMTPat (contains (restrict ks m) k)]


type Equal: #key:Type -> #value:Type -> t key value -> t key value -> Type

val lemma_equal_intro: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (forall k. sel m1 k = sel m2 k /\
                                                  contains m1 k = contains m2 k))
                       (ensures (Equal m1 m2))
                       [SMTPatT (Equal m1 m2)]

val lemma_equal_elim: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma (requires (Equal m1 m2)) (ensures  (m1 = m2))
                      [SMTPatT (Equal m1 m2)]

val lemma_equal_refl: #key:Type -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma  (requires (m1 = m2)) (ensures  (Equal m1 m2))
		      [SMTPatT (Equal m1 m2)]


let const_on (#key:Type) (#value:Type) (dom:set key) (v:value) = restrict dom (const v)

opaque type DisjointDom (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

opaque type HasDom (#key:Type) (#value:Type) (m:t key value) (dom:set key) =
  (forall x. contains m x <==> mem x dom)

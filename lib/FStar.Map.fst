module FStar.Map
open FStar.Set
open FStar.FunctionalExtensionality


type t (key:Type) (value:Type) = {
  mappings: key -> Tot value;
  domain:   key -> Tot bool
}

val sel: #key:Type -> #value:Type -> t key value -> key -> Tot value
val upd: #key:Type -> #value:Type -> t key value -> key -> value -> Tot (t key value)
val const: #key:Type -> #value:Type -> value -> Tot (t key value)
val concat: #key:Type -> #value:Type -> t key value -> t key value -> Tot (t key value)
val contains: #key:Type -> #value:Type -> t key value -> key -> Tot bool
val restrict: #key:Type -> #value:Type -> set key -> t key value -> Tot (t key value)

let sel m k = m.mappings k
let upd m k v = {
  mappings = (fun x -> if x = k then v else m.mappings x);
  domain =   (fun x -> x = k || m.domain x)
}
let const v = {
  mappings = (fun _ -> v);
  domain =   (fun _ -> true)
}
let concat m1 m2 = {
  mappings = (fun x -> if m2.domain x then m2.mappings x else m1.mappings x);
  domain =   (fun x -> m1.domain x || m2.domain x)
}
let contains m k = m.domain k
let restrict s m = {
  mappings = m.mappings;
  domain =   (fun x -> mem x s && contains m x)
}

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
                         Lemma (requires True) (ensures (contains (restrict ks m) k == (mem k ks && contains m k)))
                         [SMTPat (contains (restrict ks m) k)]

let lemma_SelUpd1 m k v        = ()
let lemma_SelUpd2 m k1 k2 v    = ()
let lemma_SelConst v k         = ()
let lemma_SelRestrict m ks k   = ()
let lemma_SelConcat1 m1 m2 k   = ()
let lemma_SelConcat2 m1 m2 k   = ()
let lemma_InDomUpd1 m k1 k2 v  = ()
let lemma_InDomUpd2 m k1 k2 v  = ()
let lemma_InDomConstMap v k    = ()
let lemma_InDomConcat m1 m2 k  = ()
let lemma_InDomRestrict m ks k = ()

type Equal (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    FEq m1.mappings m2.mappings /\ FEq m1.domain m2.domain


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

let lemma_equal_intro m1 m2 = ()
let lemma_equal_elim m1 m2  = ()
let lemma_equal_refl m1 m2  = ()

let const_on (#key:Type) (#value:Type) (dom:set key) (v:value) = restrict dom (const v)

opaque type DisjointDom (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

opaque type HasDom (#key:Type) (#value:Type) (m:t key value) (dom:set key) =
  (forall x. contains m x <==> mem x dom)

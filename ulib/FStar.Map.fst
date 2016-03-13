module FStar.Map
open FStar.Set
open FStar.FunctionalExtensionality

abstract type t (key:Type) (value:Type) = {
  mappings: key -> Tot value;
  domain:   key -> Tot bool
}

abstract val sel: t 'key 'value -> 'key -> Tot 'value
abstract val upd: t 'key 'value -> 'key -> 'value -> Tot (t 'key 'value)
abstract val const: 'value -> Tot (t 'key 'value)
abstract val concat: t 'key 'value -> t 'key 'value -> Tot (t 'key 'value)
abstract val contains: t 'key 'value -> 'key -> Tot bool
abstract val restrict: set 'key -> t 'key 'value -> Tot (t 'key 'value)

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

abstract val lemma_SelUpd1: m:t 'key 'value -> k:'key -> v:'value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k = v))
		   [SMTPat (sel (upd m k v) k)]

abstract val lemma_SelUpd2: m:t 'key 'value -> k1:'key -> k2:'key -> v:'value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 = sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

abstract val lemma_SelConst: v:'value -> k:'key ->
                    Lemma (requires True) (ensures (sel (const v) k == v))
                    [SMTPat (sel (const v) k)]

abstract val lemma_SelRestrict: m:t 'key 'value -> ks:set 'key -> k:'key ->
                       Lemma (requires True) (ensures (mem k ks ==> sel (restrict ks m) k == sel m k))
                       [SMTPat (sel (restrict ks m) k)]

abstract val lemma_SelConcat1: m1:t 'key 'value -> m2:t 'key 'value -> k:'key ->
                      Lemma (requires True) (ensures (contains m2 k ==> sel (concat m1 m2) k==sel m2 k))
                      [SMTPat (sel (concat m1 m2) k)]

abstract val lemma_SelConcat2: m1:t 'key 'value -> m2:t 'key 'value -> k:'key ->
                      Lemma (requires True) (ensures (not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k))
                      [SMTPat (sel (concat m1 m2) k)]

abstract val lemma_InDomUpd1: m:t 'key 'value -> k1:'key -> k2:'key -> v:'value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

abstract val lemma_InDomUpd2: m:t 'key 'value -> k1:'key -> k2:'key -> v:'value ->
                     Lemma (requires True) (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
                     [SMTPat (contains (upd m k2 v) k1)]

abstract val lemma_InDomConstMap: v:'value -> k:'key ->
                         Lemma (requires True) (ensures (contains (const v) k))
                         [SMTPat (contains (const v) k)]

abstract val lemma_InDomConcat: m1:t 'key 'value -> m2:t 'key 'value -> k:'key ->
                 Lemma (requires True) (ensures (contains (concat m1 m2) k==(contains m1 k || contains m2 k)))
                 [SMTPat (contains (concat m1 m2) k)]

abstract val lemma_InDomRestrict: m:t 'key 'value -> ks:set 'key -> k:'key ->
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

abstract type equal (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    feq m1.mappings m2.mappings /\ feq m1.domain m2.domain


abstract val lemma_equal_intro: m1:t 'key 'value -> m2:t 'key 'value ->
                       Lemma (requires (forall k. sel m1 k = sel m2 k /\
                                                  contains m1 k = contains m2 k))
                       (ensures (equal m1 m2))
                       [SMTPatT (equal m1 m2)]

abstract val lemma_equal_elim: m1:t 'key 'value -> m2:t 'key 'value ->
                      Lemma (requires (equal m1 m2)) (ensures  (m1 = m2))
                      [SMTPatT (equal m1 m2)]

abstract val lemma_equal_refl: m1:t 'key 'value -> m2:t 'key 'value ->
                      Lemma  (requires (m1 = m2)) (ensures  (equal m1 m2))
		      [SMTPatT (equal m1 m2)]


let lemma_equal_intro m1 m2 = ()
let lemma_equal_elim m1 m2  = ()
let lemma_equal_refl m1 m2  = ()

let const_on (#key:Type) (#value:Type) (dom:set key) (v:value) = restrict dom (const v)

type disjoint_dom (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

type has_dom (#key:Type) (#value:Type) (m:t key value) (dom:set key) =
  (forall x. contains m x <==> mem x dom)


(**
F* standard library Map module. 

@summary F* stdlib Map module. 
*)
module FStar.Map
open FStar.Set
open FStar.FunctionalExtensionality

noeq abstract type t (key:eqtype) (value:Type) = {
  mappings: key -> Tot value;
  domain:   set key
}

abstract val sel: #key:eqtype -> #value:Type -> t key value -> key -> Tot value
abstract val upd: #key:eqtype -> #value:Type -> t key value -> key -> value -> Tot (t key value)
abstract val const: #key:eqtype -> #value:Type -> value -> Tot (t key value)
abstract val concat: #key:eqtype -> #value:Type -> t key value -> t key value -> Tot (t key value)
abstract val contains: #key:eqtype -> #value:Type -> t key value -> key -> Tot bool
abstract val restrict: #key:eqtype -> #value:Type -> set key -> t key value -> Tot (t key value)
abstract val domain: #key:eqtype -> #value:Type -> t key value -> Tot (set key)

let sel #key #value m k = m.mappings k
let upd #key #value m k v = {
  mappings = (fun x -> if x = k then v else m.mappings x);
  domain =   union m.domain (singleton k)
}
let const #key #value v = {
  mappings = (fun _ -> v);
  domain =   complement empty
}

let concat #key #value m1 m2 = {
  mappings = (fun x -> if mem x m2.domain then m2.mappings x else m1.mappings x);
  domain =   union m1.domain m2.domain
}
let contains #key #value m k = mem k m.domain
let restrict #key #value s m = {
  mappings = m.mappings;
  domain =   intersect s m.domain
}
let domain #key #value m = m.domain

abstract val lemma_SelUpd1: #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
                   Lemma (requires True) (ensures (sel (upd m k v) k == v))
		   [SMTPat (sel (upd m k v) k)]

abstract val lemma_SelUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                   Lemma (requires True) (ensures (k2=!=k1 ==> sel (upd m k2 v) k1 == sel m k1))
                   [SMTPat (sel (upd m k2 v) k1)]

abstract val lemma_SelConst: #key:eqtype -> #value:Type -> v:value -> k:key ->
                    Lemma (requires True) (ensures (sel (const v) k == v))
                    [SMTPat (sel (const v) k)]

abstract val lemma_SelRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:set key -> k:key ->
                       Lemma (requires True) (ensures (mem k ks ==> sel (restrict ks m) k == sel m k))
                       [SMTPat (sel (restrict ks m) k)]

abstract val lemma_SelConcat1: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (contains m2 k ==> sel (concat m1 m2) k==sel m2 k))
                      [SMTPat (sel (concat m1 m2) k)]

abstract val lemma_SelConcat2: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                      Lemma (requires True) (ensures (not(contains m2 k) ==> sel (concat m1 m2) k==sel m1 k))
                      [SMTPat (sel (concat m1 m2) k)]

abstract val lemma_InDomUpd1: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (contains (upd m k1 v) k2 == (k1=k2 || contains m k2)))
                     [SMTPat (contains (upd m k1 v) k2)]

abstract val lemma_InDomUpd2: #key:eqtype -> #value:Type -> m:t key value -> k1:key -> k2:key -> v:value ->
                     Lemma (requires True) (ensures (k2=!=k1 ==> contains (upd m k2 v) k1 == contains m k1))
                     [SMTPat (contains (upd m k2 v) k1)]

abstract val lemma_InDomConstMap: #key:eqtype -> #value:Type -> v:value -> k:key ->
                         Lemma (requires True) (ensures (contains (const v) k))
                         [SMTPat (contains (const v) k)]

abstract val lemma_InDomConcat: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value -> k:key ->
                 Lemma (requires True) (ensures (contains (concat m1 m2) k==(contains m1 k || contains m2 k)))
                 [SMTPat (contains (concat m1 m2) k)]

abstract val lemma_InDomRestrict: #key:eqtype -> #value:Type -> m:t key value -> ks:set key -> k:key ->
                         Lemma (requires True) (ensures (contains (restrict ks m) k == (mem k ks && contains m k)))
                         [SMTPat (contains (restrict ks m) k)]

abstract val lemma_ContainsDom: #key:eqtype -> #value:Type -> m:t key value -> k:key -> 
  Lemma (requires True) (ensures (contains m k = mem k (domain m)))
                      [SMTPatOr[[SMTPat (contains m k)]; [SMTPat (mem k (domain m))]]]

abstract val lemma_UpdDomain : #key:eqtype -> #value:Type -> m:t key value -> k:key -> v:value ->
  Lemma (requires True) 
	(ensures (equal (domain (upd m k v)) (union (domain m) (singleton k))))
	[SMTPat (domain (upd m k v))]
  
let lemma_SelUpd1 #key #value m k v        = ()
let lemma_SelUpd2 #key #value m k1 k2 v    = ()
let lemma_SelConst #key #value v k         = ()
let lemma_SelRestrict #key #value m ks k   = ()
let lemma_SelConcat1 #key #value m1 m2 k   = ()
let lemma_SelConcat2 #key #value m1 m2 k   = ()
let lemma_InDomUpd1 #key #value m k1 k2 v  = ()
let lemma_InDomUpd2 #key #value m k1 k2 v  = ()
let lemma_InDomConstMap #key #value v k    = ()
let lemma_InDomConcat #key #value m1 m2 k  = ()
let lemma_InDomRestrict #key #value m ks k = ()
let lemma_ContainsDom #key #value m k      = ()
let lemma_UpdDomain #key #value m k v      = ()

abstract type equal (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) :Type0 =
    feq m1.mappings m2.mappings /\ equal m1.domain m2.domain


abstract val lemma_equal_intro: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                       Lemma (requires (forall k. sel m1 k == sel m2 k /\
                                                  contains m1 k = contains m2 k))
                       (ensures (equal m1 m2))
                       [SMTPat (equal m1 m2)]

abstract val lemma_equal_elim: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma (requires (equal m1 m2)) (ensures  (m1 == m2))
                      [SMTPat (equal m1 m2)]

abstract val lemma_equal_refl: #key:eqtype -> #value:Type -> m1:t key value -> m2:t key value ->
                      Lemma  (requires (m1 == m2)) (ensures  (equal m1 m2))
		      [SMTPat (equal m1 m2)]


let lemma_equal_intro #key #value m1 m2 = ()
let lemma_equal_elim #key #value m1 m2  = ()
let lemma_equal_refl #key #value m1 m2  = ()

let const_on (#key:eqtype) (#value:Type) (dom:set key) (v:value) = restrict dom (const v)

type disjoint_dom (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) =
    (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

type has_dom (#key:eqtype) (#value:Type) (m:t key value) (dom:set key) =
  (forall x. contains m x <==> mem x dom)

/**
@summary Partial maps with extensional equality
*/
module FStar.Map

open FStar.Set
open FStar.FunctionalExtensionality
module S = FStar.Set
module F = FStar.FunctionalExtensionality


(* The main "trick" in the representation of the type `t`
 * is to use a domain-restricted function type `key ^-> value`
 * from the FStar.FunctionalExtensionality library.
 * These restricted function types enjoy extensional equality,
 * which is necessary if Map.t is to also enjoy extensional equality.
 *)
noeq
abstract
type t (key:eqtype) (value:Type) = {
  mappings: key ^-> value;
  domain:   set key
}

let sel #key #value m k = m.mappings k

(* Since mappings are restricted functions,
   assignments to that field must use `F.on`
   to restrict the domain of the functional maps *)
let upd #key #value m k v = {
  mappings = F.on key (fun x -> if x = k then v else m.mappings x);
  domain =   S.union m.domain (singleton k)
}

(* idem *)
let const #key #value v = {
  mappings = F.on key (fun _ -> v);
  domain =   complement empty
}

let domain #key #value m = m.domain

let contains #key #value m k = mem k m.domain

(* Again, use F.on to build a domain-restricted function *)
let concat #key #value m1 m2 = {
  mappings = F.on key (fun x -> if mem x m2.domain then m2.mappings x else m1.mappings x);
  domain =   union m1.domain m2.domain
}

let restrict #key #value s m = {
  mappings = m.mappings;
  domain =   intersect s m.domain
}

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

let equal (#key:eqtype) (#value:Type) (m1:t key value) (m2:t key value) :Type0 =
    F.feq m1.mappings m2.mappings /\
    S.equal m1.domain m2.domain

let lemma_equal_intro #key #value m1 m2 = ()
let lemma_equal_elim #key #value m1 m2  = ()
let lemma_equal_refl #key #value m1 m2  = ()

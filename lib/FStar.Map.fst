module FStar.Map
open Prims.PURE
open FStar.Set
open FStar.FunctionalExtensionality

type t (key:Type) (value:Type) = {
  mappings: key -> Tot value;
  domain:   key -> Tot bool
}


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

let lemma_equal_intro m1 m2 = ()
let lemma_equal_elim m1 m2  = ()
let lemma_equal_refl m1 m2  = ()

(* AR: this needs to be copied from .fsi, else get an error in wysteria.fst *)
opaque type DisjointDom (#key:Type) (#value:Type) (m1:t key value) (m2:t key value) =
    (forall x.{:pattern (contains m1 x)(* ; (contains m2 x) *)} contains m1 x ==> not (contains m2 x))

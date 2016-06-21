
open Prims
type ('Akey, 'Avalue) t =
{mappings : 'Akey  ->  'Avalue; domain : 'Akey FStar_Set.set}


let sel = (fun m k -> (m.mappings k))


let upd = (fun m k v -> {mappings = (fun x -> (match ((x = k)) with
| true -> begin
v
end
| uu____99 -> begin
(m.mappings x)
end)); domain = (FStar_Set.union m.domain (FStar_Set.singleton k))})


let const = (fun v -> {mappings = (fun uu____111 -> v); domain = (FStar_Set.complement FStar_Set.empty)})


let concat = (fun m1 m2 -> {mappings = (fun x -> (match ((FStar_Set.mem x m2.domain)) with
| true -> begin
(m2.mappings x)
end
| uu____137 -> begin
(m1.mappings x)
end)); domain = (FStar_Set.union m1.domain m2.domain)})


let contains = (fun m k -> (FStar_Set.mem k m.domain))


let restrict = (fun s m -> {mappings = m.mappings; domain = (FStar_Set.intersect s m.domain)})


let domain = (fun m -> m.domain)


let lemma_SelUpd1 = (fun m k v -> ())


let lemma_SelUpd2 = (fun m k1 k2 v -> ())


let lemma_SelConst = (fun v k -> ())


let lemma_SelRestrict = (fun m ks k -> ())


let lemma_SelConcat1 = (fun m1 m2 k -> ())


let lemma_SelConcat2 = (fun m1 m2 k -> ())


let lemma_InDomUpd1 = (fun m k1 k2 v -> ())


let lemma_InDomUpd2 = (fun m k1 k2 v -> ())


let lemma_InDomConstMap = (fun v k -> ())


let lemma_InDomConcat = (fun m1 m2 k -> ())


let lemma_InDomRestrict = (fun m ks k -> ())


let lemma_ContainsDom = (fun m k -> ())


let lemma_UpdDomain = (fun m k v -> ())


type ('Akey, 'Avalue, 'Am1, 'Am2) equal =
(Prims.unit, Prims.unit) Prims.l_and


let lemma_equal_intro = (fun m1 m2 -> ())


let lemma_equal_elim = (fun m1 m2 -> ())


let lemma_equal_refl = (fun m1 m2 -> ())


let const_on = (fun dom v -> (restrict dom (const v)))


type ('Akey, 'Avalue, 'Am1, 'Am2) disjoint_dom =
Prims.unit


type ('Akey, 'Avalue, 'Am, 'Adom) has_dom =
Prims.unit





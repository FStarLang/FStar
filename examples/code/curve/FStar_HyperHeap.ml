
open Prims

type rid =
Prims.int Prims.list


type t =
(rid, FStar_Heap.heap) FStar_Map.t


let root : rid = []


type ('Aid, 'Aa) rref =
'Aa FStar_Heap.ref


let as_ref = (fun id r -> r)


let ref_as_rref = (fun i r -> (Obj.magic (())))


let lemma_as_ref_inj = (fun i r -> ())


let rec includes : rid  ->  rid  ->  Prims.bool = (fun r1 r2 -> (match ((r1 = r2)) with
| true -> begin
true
end
| uu____62 -> begin
(match (((FStar_List_Tot.length r2) > (FStar_List_Tot.length r1))) with
| true -> begin
(includes r1 (Prims.___Cons___tl r2))
end
| uu____68 -> begin
false
end)
end))


let disjoint : rid  ->  rid  ->  Prims.bool = (fun i j -> ((not ((includes i j))) && (not ((includes j i)))))


let rec lemma_aux : rid  ->  rid  ->  Prims.unit = (fun k i -> ())


let rec lemma_disjoint_includes : rid  ->  rid  ->  rid  ->  Prims.unit = (fun i j k -> ())


let extends : rid  ->  rid  ->  Prims.bool = (fun r0 r1 -> ((Prims.is_Cons r0) && ((Prims.___Cons___tl r0) = r1)))


let parent : rid  ->  rid = (fun r -> (Prims.___Cons___tl r))


let lemma_includes_refl : rid  ->  Prims.unit = (fun i -> ())


let lemma_extends_includes : rid  ->  rid  ->  Prims.unit = (fun i j -> ())


let lemma_extends_disjoint : rid  ->  rid  ->  rid  ->  Prims.unit = (fun i j k -> ())


let lemma_extends_parent : rid  ->  Prims.unit = (fun i -> ())


let lemma_extends_not_root : rid  ->  rid  ->  Prims.unit = (fun i j -> ())


let lemma_extends_only_parent : rid  ->  rid  ->  Prims.unit = (fun i j -> ())


let test0 : Prims.unit = ()


let test1 : rid  ->  rid  ->  Prims.unit = (fun r1 r2 -> ())


type ('Ai, 'Am0, 'Am1) fresh_region =
(Prims.unit, Prims.unit Prims.b2t) Prims.l_and


let sel = (fun i m r -> (FStar_Heap.sel (FStar_Map.sel m i) (as_ref i r)))


let upd = (fun i m r v -> (FStar_Map.upd m i (FStar_Heap.upd (FStar_Map.sel m i) (as_ref i r) v)))


let mod_set : rid FStar_Set.set  ->  rid FStar_Set.set = (Obj.magic ((fun __246 -> ())))


type ('As, 'Am0, 'Am1) modifies =
((rid, FStar_Heap.heap, Prims.unit, Prims.unit) FStar_Map.equal, Prims.unit Prims.b2t) Prims.l_and


type ('As, 'Am0, 'Am1) modifies_just =
((rid, FStar_Heap.heap, Prims.unit, Prims.unit) FStar_Map.equal, Prims.unit Prims.b2t) Prims.l_and


type ('Ar, 'Am0, 'Am1) modifies_one =
(Prims.unit, Prims.unit, Prims.unit) modifies_just


type ('As, 'Am0, 'Am1) equal_on =
(Prims.unit, (rid, FStar_Heap.heap, Prims.unit, Prims.unit) FStar_Map.equal) Prims.l_and


let lemma_modifies_just_trans : t  ->  t  ->  t  ->  rid FStar_Set.set  ->  rid FStar_Set.set  ->  Prims.unit = (fun m1 m2 m3 s1 s2 -> ())


let lemma_modifies_trans : t  ->  t  ->  t  ->  rid FStar_Set.set  ->  rid FStar_Set.set  ->  Prims.unit = (fun m1 m2 m3 s1 s2 -> ())


let rec lemma_includes_trans : rid  ->  rid  ->  rid  ->  Prims.unit = (fun i j k -> ())


let lemma_modset : rid  ->  rid  ->  Prims.unit = (fun i j -> ())


let lemma_modifies_includes : t  ->  t  ->  rid  ->  rid  ->  Prims.unit = (fun m1 m2 s1 s2 -> ())


let lemma_modifies_includes2 : t  ->  t  ->  rid FStar_Set.set  ->  rid FStar_Set.set  ->  Prims.unit = (fun m1 m2 s1 s2 -> ())


let lemma_disjoint_parents : rid  ->  rid  ->  rid  ->  rid  ->  Prims.unit = (fun pr r ps s -> ())


let contains_ref = (fun i r m -> ((FStar_Map.contains m i) && (FStar_Heap.contains (FStar_Map.sel m i) (as_ref i r))))


type ('Aa, 'Ai, 'Ar, 'Am0, 'Am1) fresh_rref =
(Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_and


type ('Ar, 'As, 'Ah0, 'Ah1) modifies_rref =
(Prims.unit, Prims.unit, Prims.unit) FStar_Heap.modifies


let lemma_include_cons : rid  ->  rid  ->  Prims.unit = (fun i j -> ())


type 'Am map_invariant =
Prims.unit


let lemma_extends_fresh_disjoint : rid  ->  rid  ->  rid  ->  rid  ->  t  ->  t  ->  Prims.unit = (fun i j ipar jpar m0 m1 -> ())


type ('As1, 'As2) disjoint_regions =
Prims.unit


let extends_parent : rid  ->  rid  ->  Prims.unit = (fun tip r -> ())


let includes_child : rid  ->  rid  ->  Prims.unit = (fun tip r -> ())






open Prims
type 'Aa seq =
| MkSeq of Prims.nat * (Prims.nat  ->  'Aa)


let ___MkSeq___length = (fun projectee -> (match ((Obj.magic (projectee))) with
| MkSeq (length, contents) -> begin
length
end))


let ___MkSeq___contents = (fun projectee -> (match ((Obj.magic (projectee))) with
| MkSeq (length, contents) -> begin
contents
end))


let length = (fun s -> (___MkSeq___length s))


let index = (fun s i -> (___MkSeq___contents s i))


let create = (fun len v -> MkSeq (len, (fun i -> v)))


let exFalso0 = (Obj.magic ((fun n -> ())))


let createEmpty = (fun uu____129 -> MkSeq ((Prims.parse_int "0"), (fun i -> (exFalso0 i))))


let upd = (fun s n v -> MkSeq ((length s), (fun i -> (match ((i = n)) with
| true -> begin
v
end
| uu____179 -> begin
(index s i)
end))))


let append = (fun s1 s2 -> MkSeq (((length s1) + (length s2)), (fun x -> (match ((x < (length s1))) with
| true -> begin
(index s1 x)
end
| uu____214 -> begin
(index s2 (x - (length s1)))
end))))


let op_At_Bar = (fun s1 s2 -> (append s1 s2))


let slice = (fun s i j -> MkSeq ((j - i), (fun x -> (index s (x + i)))))


let lemma_create_len = (fun n i -> ())


let lemma_len_upd = (fun n v s -> ())


let lemma_len_append = (fun s1 s2 -> ())


let lemma_len_slice = (fun s i j -> ())


let lemma_index_create = (fun n v i -> ())


let lemma_index_upd1 = (fun n v s -> ())


let lemma_index_upd2 = (fun n v s i -> ())


let lemma_index_app1 = (fun s1 s2 i -> ())


let lemma_index_app2 = (fun s2 s2 i -> ())


let lemma_index_slice = (fun s i j k -> ())


type ('Aa, 'As1, 'As2) equal =
(Prims.unit Prims.b2t, Prims.unit) Prims.l_and


let lemma_eq_intro = (fun s1 s2 -> ())


let lemma_eq_refl = (fun s1 s2 -> ())


let lemma_eq_elim = (fun s1 s2 -> ())






type 'a seq =
{contents : Support.Prims.nat  ->  'a; length : Support.Prims.nat}

let length = (fun s -> s.length)

let create = (fun len v -> {contents = (fun i -> v); length = len})

let index = (fun s i -> (s.contents i))

let upd = (fun s n v -> {contents = (fun i -> if (i = n) then begin
v
end else begin
(s.contents i)
end); length = s.length})

let append = (fun s1 s2 -> {contents = (fun x -> if (x < s1.length) then begin
(s1.contents x)
end else begin
(s2.contents (x - s1.length))
end); length = (s1.length + s2.length)})

let slice = (fun s i j -> {contents = (fun x -> (s.contents (x + i))); length = (j - i)})

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

let lemma_eq_intro = (fun s1 s2 -> ())

let lemma_eq_refl = (fun s1 s2 -> ())

let lemma_eq_elim = (fun s1 s2 -> ())





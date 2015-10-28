
open Prims
type ' a cmp =
' a  ->  ' a  ->  Prims.bool

let rec sorted = (fun f l -> (match (l) with
| [] -> begin
true
end
| x::[] -> begin
true
end
| x::y::tl -> begin
(((f x y) && (x <> y)) && (sorted f ((y)::tl)))
end))

type (' a, ' f) ordset =
' a Prims.list

let mem = (fun f x s -> (FStar_List.mem x s))

let rec set_props = (fun f s -> ())

let hd_unique = (fun f s -> ())

let empty = (fun f -> [])

let rec insert' = (fun f x s -> (match (s) with
| [] -> begin
(x)::[]
end
| hd::tl -> begin
if (x = hd) then begin
(hd)::tl
end else begin
if (f x hd) then begin
(x)::(hd)::tl
end else begin
(hd)::(insert' f x tl)
end
end
end))

let rec union = (fun f s1 s2 -> (match (s1) with
| [] -> begin
s2
end
| hd::tl -> begin
(union f tl (insert' f hd s2))
end))

let rec intersect = (fun f s1 s2 -> (match (s1) with
| [] -> begin
[]
end
| hd::tl -> begin
if (mem f hd s2) then begin
(insert' f hd (intersect f tl s2))
end else begin
(intersect f tl s2)
end
end))

let choose = (fun f s -> (match (s) with
| [] -> begin
None
end
| x::_11_87 -> begin
Some (x)
end))

let rec remove' = (fun f x s -> (match (s) with
| [] -> begin
[]
end
| hd::tl -> begin
if (x = hd) then begin
tl
end else begin
(hd)::(remove' f x tl)
end
end))

let remove = (fun f x s -> (remove' f x s))

let size = (fun f s -> (FStar_List.length s))

let rec subset = (fun f s1 s2 -> (match ((s1, s2)) with
| ([], _11_116) -> begin
true
end
| (hd::tl, hd'::tl') -> begin
if ((f hd hd') && (hd = hd')) then begin
(subset f tl tl')
end else begin
if ((f hd hd') && (not ((hd = hd')))) then begin
false
end else begin
(subset f s1 tl')
end
end
end
| (_11_126, _11_128) -> begin
false
end))

let singleton = (fun f x -> (x)::[])

let eq_helper = (fun f x _11_147 -> ())

let rec eq_lemma = (fun f s1 s2 -> ())

let mem_empty = (fun f x -> ())

let mem_singleton = (fun f x y -> ())

let rec insert_mem = (fun f x y s -> ())

let rec mem_union = (fun f x s1 s2 -> ())

let rec mem_intersect = (fun f x s1 s2 -> ())

let rec subset_implies_mem = (fun f s1 s2 -> ())

let rec mem_implies_subset = (fun f s1 s2 -> ())

let mem_subset = (fun f s1 s2 -> ())

let choose_empty = (fun f -> ())

let choose_s = (fun f s -> ())

let rec mem_remove = (fun f x y s -> ())

let rec eq_remove = (fun f x s -> ())

let size_empty = (fun f s -> ())

let rec size_remove = (fun f x s -> ())

let rec size_singleton = (fun f x -> ())

let rec subset_size = (fun f x y -> ())






let rec list_exists = (fun f l -> (match (l) with
| [] -> begin
false
end
| x::xs -> begin
((f x) || (Obj.magic (list_exists (Obj.magic xs))))
end))

let rec list_find = (fun f l -> (match (l) with
| [] -> begin
None
end
| x::xs -> begin
(match ((f x)) with
| true -> begin
Some (x)
end
| false -> begin
(Obj.magic (list_find (Obj.magic xs)))
end)
end))

let rec string_make = (fun n c -> (match ((n = 0)) with
| true -> begin
""
end
| false -> begin
(let _133_15 = (string_make (n - 1) c)
in (Prims.strcat c _133_15))
end))





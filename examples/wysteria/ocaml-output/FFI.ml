
open Prims
let empty = (fun _25_5 -> (FStar_OrdSet.empty Prins.p_cmp))

let mem = (fun p s -> (FStar_OrdSet.mem ((fun p s -> Prins.p_cmp) p s) p s))

type (' eps1, ' eps2) l__Equal =
(Prins.prin, Prims.unit Prims.b2t) Prims.l__Forall

let singleton = (fun p -> (let s = (FStar_OrdSet.singleton ((fun p -> ((fun p -> Prins.p_cmp) p)) p) p)
in (let _25_20 = ()
in s)))

let subset = (fun s1 s2 -> (FStar_OrdSet.subset ((fun s1 s2 -> Prins.p_cmp) s1 s2) s1 s2))

let union = (fun s1 s2 -> (let s = (FStar_OrdSet.union ((fun s1 s2 -> Prins.p_cmp) s1 s2) s1 s2)
in (let _25_35 = ()
in s)))

let size = (fun s -> (FStar_OrdSet.size ((fun s -> Prins.p_cmp) s) s))

let choose = (fun s -> (Prims.___Some___v (FStar_OrdSet.choose ((fun s -> Prins.p_cmp) s) s)))

let remove = (fun p s -> (FStar_OrdSet.remove ((fun p s -> Prins.p_cmp) p s) p s))

let eq_lemma = (fun s1 s2 -> ())

let read_int = (fun x -> (let _25_54 = (FStar_IO.print_string "Enter input: ")
in (FStar_IO.input_int ())))

let read_int_tuple = (fun x -> (let fst = (FStar_IO.input_int ())
in (let snd = (FStar_IO.input_int ())
in (fst, snd))))

let read_int_list = (fun _25_59 -> (let rec helper = (fun acc -> (let x = (FStar_IO.input_int ())
in if (x = 0) then begin
acc
end else begin
(helper ((x)::acc))
end))
in (helper [])))

let print_newline = (fun _25_64 -> (FStar_IO.print_newline ()))

let print_string = (fun s -> (let _25_67 = (FStar_IO.print_string s)
in (print_newline ())))

let print_int = (fun n -> (let _25_70 = (print_string (Prims.string_of_int n))
in (print_newline ())))

let print_bool = (fun b -> (let _25_73 = (print_string (Prims.string_of_bool b))
in (print_newline ())))

let print_int_list = (fun l -> (let print_string = (fun s -> (FStar_IO.print_string s))
in (let print_int = (fun i -> (print_string (Prims.string_of_int i)))
in (let _25_80 = (print_string "[ ")
in (let _25_85 = (FStar_List.iter (fun i -> (let _25_83 = (print_int i)
in (print_string "; "))) l)
in (let _25_87 = (print_string " ]")
in (print_newline ())))))))

let slice_id = (fun p c -> c)

let compose_ids = (fun x _25_94 -> x)

let slice_id_sps = (fun p x -> x)

let mk_tuple = (fun x y -> (x, y))

let slice_tuple = (fun f g p t -> ((f p (Prims.fst t)), (g p (Prims.snd t))))

let compose_tuples = (fun f g p1 p2 -> ((f (Prims.fst p1) (Prims.fst p2)), (g (Prims.snd p1) (Prims.snd p2))))

let slice_tuple_sps = (fun f g ps t -> ((f ps (Prims.fst t)), (g ps (Prims.snd t))))

let mk_none = (fun _25_122 -> None)

let mk_some = (fun x -> Some (x))

let slice_option = (fun f p _25_1 -> (match (_25_1) with
| None -> begin
None
end
| Some (x) -> begin
Some ((f p x))
end))

let compose_options = (fun f x y -> (match ((x, y)) with
| (None, None) -> begin
None
end
| (Some (x'), Some (y')) -> begin
Some ((f x' y'))
end))

let slice_option_sps = (fun f ps _25_2 -> (match (_25_2) with
| None -> begin
None
end
| Some (x) -> begin
Some ((f ps x))
end))

let mk_nil = (fun _25_156 -> [])

let mk_cons = (fun x l -> (x)::l)

let slice_list = (fun f p l -> (FStar_List_Tot.map (f p) l))

let rec compose_lists = (fun f l1 l2 -> (match ((l1, l2)) with
| (x1::tl1, x2::tl2) -> begin
((f x1 x2))::(compose_lists f tl1 tl2)
end
| (_25_181, _25_183) -> begin
[]
end))

let slice_list_sps = (fun f ps l -> (FStar_List_Tot.map (f ps) l))

let hd_of_cons = (fun _25_3 -> (match (_25_3) with
| hd::_25_194 -> begin
hd
end))

let tl_of_cons = (fun _25_4 -> (match (_25_4) with
| _25_203::tl -> begin
tl
end))

let length = (fun l -> (FStar_List_Tot.length l))





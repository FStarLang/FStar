
open Prims
let mem_empty = (fun x -> ())

let rec rev_acc_length = (fun l acc -> ())

let rev_length = (fun l -> ())

let rec rev_acc_mem = (fun l acc x -> ())

let rev_mem = (fun l x -> ())

let append_nil_l = (fun l -> ())

let rec append_l_nil = (fun _9_1 -> ())

let append_cons_l = (fun hd tl l -> ())

let rec append_l_cons = (fun hd tl l -> ())

let rec append_assoc = (fun l1 l2 l3 -> ())

let rec append_length = (fun l1 l2 -> ())

let rec append_mem = (fun l1 l2 a -> ())

let rec append_mem_forall = (fun l1 l2 -> ())

let rec append_count = (fun l1 l2 a -> ())

let rec append_count_forall = (fun l1 l2 -> ())

let append_eq_nil = (fun l1 l2 -> ())

let append_eq_singl = (fun l1 l2 x -> ())

let rec append_inv_head = (fun l l1 l2 -> ())

let rec append_inv_tail = (fun l l1 l2 -> ())

let rec rev' = (fun _9_2 -> (match (_9_2) with
| [] -> begin
[]
end
| hd::tl -> begin
(FStar_List.append (rev' tl) ((hd)::[]))
end))

let rev'T = rev'

let rec rev_acc_rev' = (fun l acc -> ())

let rev_rev' = (fun l -> ())

let rec rev'_append = (fun l1 l2 -> ())

let rev_append = (fun l1 l2 -> ())

let rec rev'_involutive = (fun _9_3 -> ())

let rev_involutive = (fun l -> ())

let rec rev'_list_ind = (fun p _9_4 -> ())

let rev_ind = (fun p l -> ())

let rec mapT_lemma = (fun f l -> ())

let partition_length = (fun f l -> ())

let rec partition_mem = (fun f l x -> ())

let rec partition_mem_forall = (fun f l -> ())

let rec partition_mem_p_forall = (fun p l -> ())

let rec partition_count = (fun f l x -> ())

let rec partition_count_forall = (fun f l -> ())

let rec sortWithT_permutation = (fun f l -> ())

let rec sorted = (fun f _9_5 -> (match (_9_5) with
| ([]) | (_::[]) -> begin
true
end
| x::y::tl -> begin
((f x y) && (sorted f ((y)::tl)))
end))

let rec append_sorted = (fun f l1 l2 pivot -> ())

let rec sortWithT_sorted = (fun f l -> ())





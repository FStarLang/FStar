(* We give an implementation here using OCaml's BatList,
   which privide tail-recursive versions of most functions *)

include FStar_List_Tot_Base

let nth l i = BatList.nth l (Z.to_int i)
let iter = BatList.iter
let iteri_aux _ _ _ = failwith "FStar_List.ml: Not implemented: iteri_aux"
let iteri f l = BatList.iteri (fun i x -> f (Z.of_int i) x) l
let mapT = map
let map2 = BatList.map2
let rec map3 f l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (f x y z)::(map3 f xs ys zs)
  | _, _, _ -> failwith "The lists do not have the same length"
let fold_left2 _ _ _ _ = failwith "FStar_List.ml: Not implemented: fold_left2"
let forall2 = BatList.for_all2
let zip = BatList.combine
let splitAt x l = BatList.split_at (Z.to_int x) l
let filter_map = BatList.filter_map
let index f l =
  Z.of_int (fst (BatList.findi (fun _ x -> f x) l))

(* Other functions not part of FStar.List.fst *)
let memT = mem
let rev_append = BatList.rev_append
let rec zip3 l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3) :: (zip3 t1 t2 t3)
  | _ -> failwith "zip3"
let unique = BatList.unique

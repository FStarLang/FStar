(* We give an implementation here using OCaml's BatList,
   which provides tail-recursive versions of most functions *)
include FStar_List

let isEmpty l = l = []
let singleton x = [x]
let mem = BatList.mem
let length l = Z.of_int (BatList.length l)
let rev = BatList.rev
let iter2 = BatList.iter2
let append = BatList.append
let rev_append = BatList.rev_append
let fold_right2 = BatList.fold_right2
let rev_map_onto f l acc = fold_left (fun acc x -> f x :: acc) acc l
let last_opt l = List.fold_left (fun _ x -> Some x) None l
let unzip = BatList.split
let rec unzip3 = function
  | [] -> ([],[],[])
  | (x,y,z)::xyzs ->
     let (xs,ys,zs) = unzip3 xyzs in
     (x::xs,y::ys,z::zs)
let find = tryFind
let flatten = BatList.flatten
let concat = flatten
let split = unzip
let existsb f l = BatList.exists f l
let existsML f l = BatList.exists f l
let contains x l = BatList.exists (fun y -> x = y) l
let rec zip3 l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3) :: (zip3 t1 t2 t3)
  | _ -> failwith "zip3"
let unique = BatList.unique
let span = BatList.span
let deduplicate (f:'a -> 'a -> bool) (l:'a list) : 'a list = BatList.unique ~eq:f l
let fold_left_map = BatList.fold_left_map

(* We give an implementation here using OCaml's BatList,
   which provide tail-recursive versions of most functions.
   The rest we implement manually. *)

let isEmpty l = l = []
let hd = BatList.hd
let tail = BatList.tl
let tl = BatList.tl

let rec last = function
  | x :: [] -> x
  | _ :: tl -> last tl

let rec init = function
  | _ :: [] -> []
  | hd :: tl -> hd :: init tl

let length l = Z.of_int (BatList.length l)
let nth l i = try Some (BatList.nth l (Z.to_int i)) with _ -> None
let index l i = BatList.nth l (Z.to_int i)

let rec count x = function
  | [] -> Prims.int_zero
  | hd::tl -> if x=hd then Z.add Prims.int_one (count x tl) else count x tl

let rev_acc l r = BatList.rev_append l r
let rev = BatList.rev
let append = BatList.append
let op_At = append
let snoc (x, y) = append x [y]
let flatten = BatList.flatten
let map = BatList.map
let mapi_init _ _ _ = failwith "FStar_List_Tot_Base.ml: Not implemented: mapi_init"
let mapi f l = BatList.mapi (fun i x -> f (Z.of_int i) x) l
let concatMap f l = flatten (map f l)
let fold_left = BatList.fold_left
let fold_right = BatList.fold_right
let fold_left2 = BatList.fold_left2
let mem = BatList.mem
type ('a, 'b, 'c) memP = unit
let contains x l = BatList.exists (fun y -> x = y) l
let existsb f l = BatList.exists f l
let find f l = try Some (BatList.find f l) with | Not_found -> None
let filter = BatList.filter
let for_all = BatList.for_all
let collect f l = BatList.flatten (BatList.map f l)
let tryFind = find
let tryPick f l = try f (BatList.find (fun x -> f x <> None) l) with | Not_found -> None
let choose = BatList.filter_map
let partition = BatList.partition
let subset la lb = BatList.subset (fun x y -> if x = y then 0 else 1) la lb

let rec noRepeats = function
  | [] -> true
  | h :: tl -> not (mem h tl) && noRepeats tl

let assoc x l = match List.assoc x l with exception Not_found -> None | x -> Some x
let split = BatList.split
let unzip = split
let rec unzip3 = function
  | [] -> ([],[],[])
  | (x,y,z)::xyzs ->
     let (xs,ys,zs) = unzip3 xyzs in
     (x::xs,y::ys,z::zs)

let splitAt n l = BatList.split_at (Z.to_int n) l
let unsnoc l = let l1, l2 = splitAt (Z.sub (length l) Z.one) l in l1, hd l2
let split3 l i = let a, a1 = splitAt i l in let b :: c = a1 in a, b, c

let bool_of_compare f x y = Z.gt (f x y) Z.zero
let compare_of_bool =
  fun rel -> fun x -> fun y -> if (rel x y) then Z.one else (if x = y then Z.zero else (Z.neg Z.one))
let sortWith f l = BatList.sort (fun x y -> Z.to_int (f x y)) l
let list_unref l = l
let list_ref _ l = l
let list_refb _ l = l

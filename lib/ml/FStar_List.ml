(* We give an implementation here using OCaml's BatList,
   which privide tail-recursive versions of most functions *)
let isEmpty l = l = []
let mem = BatList.mem
let memT = mem
let hd = BatList.hd
let tl = BatList.tl
let tail = BatList.tl
let nth = BatList.nth
let length = BatList.length
let rev = BatList.rev
let map = BatList.map
let mapT = map
let mapi = BatList.mapi
let map2 = BatList.map2
let rec map3 f l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x::xs, y::ys, z::zs -> (f x y z)::(map3 f xs ys zs)
  | _, _, _ -> failwith "The lists do not have the same length"
let iter = BatList.iter
let partition = BatList.partition
let append = BatList.append
let rev_append = BatList.rev_append
let fold_left = BatList.fold_left
let fold_right = BatList.fold_right
let fold_left2 = BatList.fold_left2
let collect f l = BatList.flatten (BatList.map f l)
let unzip = BatList.split
let rec unzip3 = function
  | [] -> ([],[],[])
  | (x,y,z)::xyzs ->
     let (xs,ys,zs) = unzip3 xyzs in
     (x::xs,y::ys,z::zs)
let filter = BatList.filter
let sortWith = BatList.sort
let for_all = BatList.for_all
let forall2 = BatList.for_all2
let tryFind f l = try Some (BatList.find f l) with | Not_found -> None
let find = tryFind
let tryPick f l = try f (BatList.find (fun x -> f x <> None) l) with | Not_found -> None
let flatten = BatList.flatten
let split = unzip
let choose = BatList.filter_map
let exists_ f l = BatList.exists f l
let contains x l = BatList.exists (fun y -> x = y) l
let zip = BatList.combine
let rec zip3 l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | h1::t1, h2::t2, h3::t3 -> (h1, h2, h3) :: (zip3 t1 t2 t3)
  | _ -> failwith "zip3"
let rec unzip3 l =
  match l with
  | [] -> [],[],[]
  | (x,y,z)::t -> let u,v,w = unzip3 t in x::u,y::v,z::w
let unique = BatList.unique


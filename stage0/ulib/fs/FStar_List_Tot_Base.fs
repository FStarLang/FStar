module FStar_List_Tot_Base
open Prims

let isEmpty l = List.isEmpty l
let hd = List.head
let tail = List.tail
let tl = List.tail
let length l : int = List.length l |> System.Numerics.BigInteger.op_Implicit
let nth l (i : Prims.nat) = try Some (List.nth l (Microsoft.FSharp.Core.Operators.int i)) with _ -> None
let index l (i : Prims.nat) = List.nth l (Microsoft.FSharp.Core.Operators.int i)
let count _ _ = failwith "FStar_List.Tot.Base.fs: Not implemented: count"
let rev_acc l r = List.fold (fun xs x -> x :: xs) r l
let rev = List.rev
let append = List.append
let op_At = append
let snoc (x, y) = append x [y]
let flatten = List.concat
let map = List.map
let mapi_init _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: mapi_init"
let mapi f l = List.mapi (fun i x -> f (System.Numerics.BigInteger.op_Implicit i) x) l
let concatMap f l = List.collect f l
let fold_left = List.fold
let fold_right = List.foldBack
let fold_left2 = List.fold2
let mem = List.contains
//type ('a, 'b, 'c) memP = NOT IMPLEMENTED
let contains x l = List.exists (fun y -> x = y) l
let existsb f l = List.exists f l
let find f l = List.tryFind f l
let filter = List.filter
let for_all = List.forall
let collect f l = List.collect f l
let tryFind = find
let tryPick f l = List.tryPick f l
let choose = List.choose
let partition = List.partition
let subset _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: subset"
let noRepeats _ = failwith "FStar.List.Tot.Base.fs: Not implemented: noRepeats"
let rec assoc x l = l |> List.tryFind (fun (h, _) -> h = x) |> Option.map snd
let split = List.unzip
let splitAt = List.splitAt
let unzip = List.unzip

let unzip3 = List.unzip3
let bool_of_compare _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: bool_of_compare"
let compare_of_bool _ _ _ = failwith "FStar.List.Tot.Base.fs: Not implemented: compare_of_bool"
let sortWith (f : 'a -> 'a -> Prims.int) l = List.sortWith (fun x y -> Microsoft.FSharp.Core.Operators.int (f x y)) l
let list_unref l = l
